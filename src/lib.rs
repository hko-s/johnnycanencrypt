// SPDX-FileCopyrightText: © 2020 Kushal Das <mail@kushaldas.in>
// SPDX-License-Identifier: LGPL-3.0-or-later

use pyo3::create_exception;
use pyo3::exceptions::*;
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyDateTime, PyDict, PyList, PyTuple};
use pyo3::wrap_pyfunction;
use pyo3::PyDowncastError;

use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt;
use std::fs::File;
use std::io;
use std::io::Write;
use std::io::{Read, Seek, SeekFrom};
use std::path::Path;
use std::str;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

extern crate anyhow;
extern crate sequoia_openpgp as openpgp;
extern crate sshkeys;
extern crate tempfile;

use chrono::prelude::*;

use openpgp::armor;
use openpgp::armor::{Kind, Writer};
use openpgp::cert::prelude::*;
use openpgp::crypto::{KeyPair, SessionKey};
use openpgp::packet::signature::SignatureBuilder;
use openpgp::packet::Signature;
use openpgp::parse::stream::{
    DecryptionHelper, DecryptorBuilder, DetachedVerifierBuilder, MessageLayer, MessageStructure,
    VerificationHelper, VerifierBuilder,
};
use openpgp::parse::{PacketParser, PacketParserResult, Parse};
use openpgp::policy::Policy;
use openpgp::policy::StandardPolicy as P;
use openpgp::serialize::stream::{Armorer, Encryptor, LiteralWriter, Message, Signer};
use openpgp::serialize::Marshal;
use openpgp::serialize::MarshalInto;
use openpgp::types::KeyFlags;
use openpgp::types::ReasonForRevocation;
use openpgp::types::RevocationStatus;
use openpgp::types::SignatureType;
use openpgp::types::SymmetricAlgorithm;
use openpgp::KeyHandle;
use openpgp::Packet;
use openpgp_card::card_do::TouchPolicy;
use openpgp_card::KeyType;
use openpgp_card_sequoia::state::Open;
use openpgp_card_sequoia::Card;

mod scard;

// Our CryptoError exception
create_exception!(johnnycanencrypt, CryptoError, PyException);

// Our SameKeyError exception
create_exception!(johnnycanencrypt, SameKeyError, PyException);

// Error in selecting OpenPGP applet in the card
create_exception!(johnnycanencrypt, CardError, PyException);

#[derive(Debug)]
pub struct JceError {
    msg: String,
}

/// Result Generic Type for the module.
pub type Result<T> = ::std::result::Result<T, JceError>;

impl fmt::Display for JceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.msg)
    }
}

impl std::convert::From<std::fmt::Error> for JceError {
    fn from(err: std::fmt::Error) -> JceError {
        JceError {
            msg: err.to_string(),
        }
    }
}

impl std::convert::From<openpgp_card::Error> for JceError {
    fn from(err: openpgp_card::Error) -> JceError {
        JceError {
            msg: err.to_string(),
        }
    }
}

impl std::convert::From<anyhow::Error> for JceError {
    fn from(err: anyhow::Error) -> JceError {
        JceError {
            msg: err.to_string(),
        }
    }
}

impl std::convert::From<pyo3::PyErr> for JceError {
    fn from(err: pyo3::PyErr) -> JceError {
        JceError {
            msg: err.to_string(),
        }
    }
}

impl std::convert::From<std::io::Error> for JceError {
    fn from(err: std::io::Error) -> JceError {
        JceError::new(err.to_string())
    }
}

impl std::convert::From<str::Utf8Error> for JceError {
    fn from(err: str::Utf8Error) -> JceError {
        JceError::new(err.to_string())
    }
}

impl std::convert::From<std::string::FromUtf8Error> for JceError {
    fn from(err: std::string::FromUtf8Error) -> JceError {
        JceError::new(err.to_string())
    }
}

impl std::convert::From<JceError> for PyErr {
    fn from(err: JceError) -> PyErr {
        CryptoError::new_err(err.to_string())
    }
}

impl JceError {
    fn new(msg: String) -> Self {
        JceError { msg }
    }
}

/// Finds all keys in a cert and creates a list of fingerprint, algo, bitsize
#[pyfunction]
#[pyo3(text_signature = "(certdata)")]
pub fn get_key_cipher_details(py: Python, certdata: Vec<u8>) -> Result<PyObject> {
    let cert = openpgp::Cert::from_bytes(&certdata)?;
    let list = PyList::empty(py);

    let p = &P::new();
    for key in cert.with_policy(p, None)?.keys() {
        let fp = key.fingerprint().to_hex();
        let key_algo = key.pk_algo();
        let bits = key.mpis().bits();
        let algo = key_algo.to_string().clone();
        let key_tuple = (fp.clone(), algo, bits).to_object(py);

        let key_tuple: std::result::Result<&PyTuple, PyDowncastError> =
            key_tuple.downcast::<PyTuple>(py);

        let kt = match key_tuple {
            Ok(value) => value,
            Err(msg) => {
                return Err(JceError::new(format!(
                    "Can not parse subkey for cipher details {}",
                    msg
                )));
            }
        };
        list.append(kt.clone())?;
    }

    Ok(list.into())
}

/// Returns updated key with new expiration time for subkeys
/// Takes the secret key data, a list of subkey fingerprints as str,
/// expirytime as the duration to be added as integer, and the secret key password.
#[pyfunction]
#[pyo3(text_signature = "(certdata, fingerprints, expirytime, password)")]
pub fn update_subkeys_expiry_in_cert(
    py: Python,
    certdata: Vec<u8>,
    fingerprints: Vec<String>,
    expirytime: u64,
    password: String,
) -> Result<PyObject> {
    let cert = openpgp::Cert::from_bytes(&certdata)?;

    let p = &P::new();
    let pk = cert.primary_key().key();
    let mut signer = pk
        .clone()
        .parts_into_secret()?
        .decrypt_secret(&openpgp::crypto::Password::from(password))?
        .into_keypair()?;

    // Create the binding signatures.
    let mut sigs = Vec::new();

    for key in cert.with_policy(p, None)?.keys().subkeys() {
        let fp = key.fingerprint().to_hex();
        if !fingerprints.contains(&fp) {
            continue;
        }
        // This reuses any existing backsignature.
        let sig =
            openpgp::packet::signature::SignatureBuilder::from(key.binding_signature().clone())
                .set_key_expiration_time(&key, SystemTime::now() + Duration::new(expirytime, 0))?
                .sign_subkey_binding(&mut signer, pk, &key)?;
        sigs.push(sig);
    }

    let cert = cert.insert_packets(sigs)?;
    // Now let us return the secret key as Python Bytes
    let mut buf = Vec::new();
    let mut buffer = Vec::new();

    let mut writer = Writer::new(&mut buf, Kind::SecretKey)?;
    cert.as_tsk().serialize(&mut buffer)?;
    writer.write_all(&buffer)?;
    writer.finalize()?;

    // Let us return the cert data which can be saved in the database
    let res = PyBytes::new(py, &buf);
    Ok(res.into())
}

#[pyfunction]
#[pyo3(text_signature = "(certdata, uid, password)")]
pub fn revoke_uid_in_cert(
    py: Python,
    certdata: Vec<u8>,
    uid: Vec<u8>,
    password: String,
) -> Result<PyObject> {
    // This is where we will store all the signing keys
    let mut cert = openpgp::Cert::from_bytes(&certdata)?;

    // To find the secret keypair
    let mut keypair = match cert
        .primary_key()
        .key()
        .clone()
        .parts_into_secret()?
        .secret()
        .is_encrypted()
    {
        true => {
            // When the secret is encrypted with a password
            cert.primary_key()
                .key()
                .clone()
                .parts_into_secret()?
                .decrypt_secret(&openpgp::crypto::Password::from(password))?
                .into_keypair()?
        }
        false => {
            // When the secret is not encrypted
            cert.primary_key()
                .key()
                .clone()
                .parts_into_secret()?
                .into_keypair()?
        }
    };

    // now let us find the user id from the cert.
    for ua in cert.clone().userids() {
        let value = ua.value().to_vec();
        if value == uid {
            // We found the uid which we can now revoke
            let sig = UserIDRevocationBuilder::new()
                .set_reason_for_revocation(ReasonForRevocation::UIDRetired, b"Revoked via code.")?
                .build(&mut keypair, &cert, ua.userid(), None)?;
            // Now merge this back
            cert = cert.insert_packets(sig.clone())?;
        }
    }

    let mut buf = Vec::new();
    let mut buffer = Vec::new();

    let mut writer = Writer::new(&mut buf, Kind::SecretKey)?;
    cert.as_tsk().serialize(&mut buffer)?;
    writer.write_all(&buffer)?;
    writer.finalize()?;

    // Let us return the cert data which can be saved in the database
    let res = PyBytes::new(py, &buf);
    Ok(res.into())
}

#[pyfunction]
#[pyo3(text_signature = "(certdata, uid, password)")]
pub fn add_uid_in_cert(
    py: Python,
    certdata: Vec<u8>,
    uid: Vec<u8>,
    password: String,
) -> Result<PyObject> {
    // This is where we will store all the signing keys
    let cert = openpgp::Cert::from_bytes(&certdata)?;

    // To find the secret keypair
    let mut keypair = match cert
        .primary_key()
        .key()
        .clone()
        .parts_into_secret()?
        .secret()
        .is_encrypted()
    {
        true => {
            // When the secret is encrypted with a password
            cert.primary_key()
                .key()
                .clone()
                .parts_into_secret()?
                .decrypt_secret(&openpgp::crypto::Password::from(password))?
                .into_keypair()?
        }
        false => {
            // When the secret is not encrypted
            cert.primary_key()
                .key()
                .clone()
                .parts_into_secret()?
                .into_keypair()?
        }
    };
    let userid = openpgp::packet::UserID::from(uid);
    let builder = openpgp::packet::signature::SignatureBuilder::new(
        openpgp::types::SignatureType::PositiveCertification,
    );
    let binding = userid.bind(&mut keypair, &cert, builder)?;
    let cert = cert.insert_packets(vec![Packet::from(userid), binding.into()])?;

    let mut buf = Vec::new();
    let mut buffer = Vec::new();

    let mut writer = Writer::new(&mut buf, Kind::SecretKey)?;
    cert.as_tsk().serialize(&mut buffer)?;
    writer.write_all(&buffer)?;
    writer.finalize()?;

    // Let us return the cert data which can be saved in the database
    let res = PyBytes::new(py, &buf);
    Ok(res.into())
}

#[pyfunction]
pub fn update_password(
    py: Python,
    certdata: Vec<u8>,
    password: String,
    newpass: String,
) -> Result<PyObject> {
    let p = P::new();
    let mut cert = openpgp::Cert::from_bytes(&certdata)?;
    let mut keys = Vec::new();
    // First let us change the password for the primary key
    let key = cert
        .primary_key()
        .key()
        .clone()
        .parts_into_secret()?
        .decrypt_secret(&openpgp::crypto::Password::from(password.clone()))?;
    let pkey = key.encrypt_secret(&openpgp::crypto::Password::from(newpass.clone()))?;

    for key in cert
        .keys()
        .subkeys()
        .with_policy(&p, None)
        .alive()
        .revoked(false)
        .map(|kd| kd.key())
    {
        let k = key
            .clone()
            .parts_into_secret()?
            .decrypt_secret(&openpgp::crypto::Password::from(password.clone()))?;
        let newk = k.encrypt_secret(&openpgp::crypto::Password::from(newpass.clone()))?;
        keys.push(newk.clone());
    }

    // First let us merge the changed primary key and then the subkeys
    cert = cert.insert_packets(Packet::from(pkey))?;
    // here we are merging the subkeys back
    for k in keys {
        cert = cert.insert_packets(Packet::from(k))?;
    }

    let mut buf = Vec::new();
    let mut buffer = Vec::new();

    let mut writer = Writer::new(&mut buf, Kind::SecretKey)?;
    cert.as_tsk().serialize(&mut buffer)?;
    writer.write_all(&buffer)?;
    writer.finalize()?;
    // Let us return the cert data which can be saved in the database
    let res = PyBytes::new(py, &buf);
    Ok(res.into())
}

#[pyfunction]
#[pyo3(text_signature = "(certdata, data, pin)")]
fn decrypt_bytes_on_card(
    _py: Python,
    _certdata: Vec<u8>,
    data: Vec<u8>,
    pin: Vec<u8>,
) -> Result<PyObject> {
    let mut result = Vec::new();
    scard::decrypt_on_card(data.as_slice(), &mut result, pin)?;

    let res = PyBytes::new(_py, &result);
    Ok(res.into())
}

#[pyfunction]
#[pyo3(text_signature = "(certdata, filepath, output, pin)")]
pub fn decrypt_file_on_card(
    _py: Python,
    _certdata: Vec<u8>,
    filepath: Vec<u8>,
    output: Vec<u8>,
    pin: Vec<u8>,
) -> Result<bool> {
    let input = File::open(str::from_utf8(&filepath[..])?)?;
    let mut outfile = File::create(str::from_utf8(&output[..])?)?;

    scard::decrypt_on_card(input, &mut outfile, pin)?;

    Ok(true)
}

#[pyfunction]
#[pyo3(text_signature = "(certdata, fh, output, pin)")]
pub fn decrypt_filehandler_on_card(
    _py: Python,
    _certdata: Vec<u8>,
    fh: PyObject,
    output: Vec<u8>,
    pin: Vec<u8>,
) -> Result<bool> {
    let filedata = fh.call_method(_py, "read", (), None)?;
    let pbytes: &PyBytes = filedata
        .as_ref(_py)
        .downcast::<PyBytes>()
        .expect("Excepted bytes");
    let data: Vec<u8> = Vec::from(pbytes.as_bytes());

    let mut outfile = File::create(str::from_utf8(&output[..])?)?;
    scard::decrypt_on_card(data.as_slice(), &mut outfile, pin)?;

    Ok(true)
}

#[pyfunction]
fn reset_yubikey() -> PyResult<bool> {
    Ok(scard::reset_yk()?)
}

#[pyfunction]
fn get_card_details(py: Python) -> PyResult<PyObject> {
    let cd = scard::get_card_details()?;

    let pd = PyDict::new(py);
    pd.set_item("serial_number", format!("{}", cd.serial))?;
    pd.set_item("name", cd.cardholder_name)?;
    pd.set_item("url", cd.url)?;
    pd.set_item("sig_f", cd.sig_fp)?;
    pd.set_item("enc_f", cd.enc_fp)?;
    pd.set_item("auth_f", cd.aut_fp)?;
    pd.set_item("PW1", cd.pw1)?;
    pd.set_item("RC", cd.rc)?;
    pd.set_item("PW3", cd.pw3)?;
    pd.set_item("signatures", cd.signature_count)?;

    Ok(pd.into())
}

/// Change user pin (PW1)
#[pyfunction]
#[pyo3(text_signature = "(adminpin, newpin)")]
pub fn change_user_pin(adminpin: Vec<u8>, newpin: Vec<u8>) -> PyResult<bool> {
    // check for minimum length of 6 chars
    if newpin.len() < 6 {
        Err(PyValueError::new_err(
            "The new pin should be 6 chars length minimum.",
        ))
    } else {
        Ok(scard::change_user_pin(adminpin, newpin)?)
    }
}

/// Change admin pin (PW3)
#[pyfunction]
#[pyo3(text_signature = "(adminpin, newadminpin)")]
pub fn change_admin_pin(adminpin: Vec<u8>, newadminpin: Vec<u8>) -> PyResult<bool> {
    // check for minimum length of 6 chars
    if newadminpin.len() < 8 {
        Err(PyValueError::new_err(
            "The new pin should be 6 chars length minimum.",
        ))
    } else {
        Ok(scard::change_admin_pin(adminpin, newadminpin)?)
    }
}

/// Sets the name of the card holder.
/// Requires the name as bytes in b"surname<<Firstname" format, and should be less than 39 in size.
/// Also requires the admin pin in bytes.
#[pyfunction]
#[pyo3(text_signature = "(name, pin)")]
pub fn set_name(name: Vec<u8>, pin: Vec<u8>) -> PyResult<bool> {
    let name = String::from_utf8(name)?;
    Ok(scard::set_name(&name, pin)?)
}

/// Sets the URL of the public key of the card.
/// Requires the URL as buytes
/// Also requires the admin pin in bytes.
#[pyfunction]
#[pyo3(text_signature = "(url, pin)")]
pub fn set_url(url: Vec<u8>, pin: Vec<u8>) -> PyResult<bool> {
    Ok(scard::set_url(url, pin)?)
}

struct Helper {
    keys: HashMap<openpgp::KeyID, KeyPair>,
}

impl Helper {
    /// Creates a Helper for the given Certs with appropriate secrets.
    fn new(p: &dyn Policy, cert: &openpgp::Cert, pass: &str) -> Self {
        // Map (sub)KeyIDs to secrets.
        let mut keys = HashMap::new();

        for ka in cert.keys().with_policy(p, None).secret() {
            // To find the secret keypair
            let keypair = match ka.key().clone().secret().is_encrypted() {
                true => {
                    // When the secret is encrypted with a password
                    ka.key()
                        .clone()
                        .decrypt_secret(&openpgp::crypto::Password::from(pass))
                        .unwrap()
                        .into_keypair()
                        .unwrap()
                }
                false => {
                    // When the secret is not encrypted
                    ka.key().clone().into_keypair().unwrap()
                }
            };
            keys.insert(ka.key().keyid(), keypair.clone());
        }
        Helper { keys }
    }
}

impl DecryptionHelper for Helper {
    fn decrypt<D>(
        &mut self,
        pkesks: &[openpgp::packet::PKESK],
        _skesks: &[openpgp::packet::SKESK],
        sym_algo: Option<SymmetricAlgorithm>,
        mut decrypt: D,
    ) -> openpgp::Result<Option<openpgp::Fingerprint>>
    where
        D: FnMut(SymmetricAlgorithm, &SessionKey) -> bool,
    {
        // Try each PKESK until we succeed.
        for pkesk in pkesks {
            let keyid = pkesk.recipient();
            // The following was done to extract the actual encrypted session key.
            // So that we can verify our code by just decrypt that on smartcard
            //let esk = pkesk.esk();
            //match esk {
            //openpgp::crypto::mpi::Ciphertext::RSA { c: myvalue } => {
            //let mut file = File::create("foo2.binary")?;
            //let value = myvalue.value();
            //file.write_all(&value[..]).unwrap();
            //}
            //_ => (),
            //};
            // If the keyid is not present, we should just skip to next pkesk
            let keypair = match self.keys.get_mut(keyid) {
                Some(keypair) => keypair,
                _ => {
                    continue;
                }
            };
            let fp = keypair.public().fingerprint();
            // now get the algo
            if pkesk
                .decrypt(keypair, sym_algo)
                .map(|(algo, session_key)| decrypt(algo, &session_key))
                .unwrap_or(false)
            {
                return Ok(Some(fp));
            }
        }
        Ok(None)
    }
}

impl VerificationHelper for Helper {
    fn get_certs(&mut self, _ids: &[openpgp::KeyHandle]) -> openpgp::Result<Vec<openpgp::Cert>> {
        Ok(vec![]) // Feed the Certs to the verifier here.
    }
    fn check(&mut self, _structure: MessageStructure) -> openpgp::Result<()> {
        Ok(())
    }
}

struct VHelper {
    cert: openpgp::Cert,
}

impl VHelper {
    /// Creates a VHelper for the given Cert for signature verification.
    fn new(cert: &openpgp::Cert) -> Self {
        let cloned = cert.clone();
        VHelper { cert: cloned }
    }
}

impl VerificationHelper for VHelper {
    fn get_certs(&mut self, _ids: &[openpgp::KeyHandle]) -> openpgp::Result<Vec<openpgp::Cert>> {
        Ok(vec![self.cert.clone()]) // Feed the Certs to the verifier here.
    }
    fn check(&mut self, structure: MessageStructure) -> openpgp::Result<()> {
        let mut good = false;
        for (i, layer) in structure.into_iter().enumerate() {
            match layer {
                MessageLayer::Encryption { .. } => (),
                MessageLayer::Compression { .. } => (),
                // First, we are interested in signatures over the
                // data or inside.
                MessageLayer::SignatureGroup { results } if i == 0 || i == 1 || i == 2 => {
                    // Finally, given a VerificationResult, which only says
                    // whether the signature checks out mathematically, we apply
                    // our policy.
                    match results.into_iter().next() {
                        Some(Ok(_)) => good = true,
                        Some(Err(e)) => return Err(openpgp::Error::from(e).into()),
                        None => return Err(anyhow::anyhow!("No signature")),
                    }
                }
                _ => {
                    return Err(anyhow::anyhow!("Unexpected message structure"));
                }
            }
        }

        if good {
            Ok(()) // Good signature.
        } else {
            Err(anyhow::anyhow!("Signature verification failed"))
        }
    }
}

// To create key pairs; from the given Cert
fn get_keys(cert: &openpgp::cert::Cert, password: String) -> Vec<openpgp::crypto::KeyPair> {
    let p = P::new();

    let mut keys = Vec::new();
    for key in cert
        .keys()
        .with_policy(&p, None)
        .alive()
        .revoked(false)
        .for_signing()
        .secret()
        .map(|kd| kd.key())
    {
        let mut key = key.clone();
        let algo = key.pk_algo();

        key.secret_mut()
            .decrypt_in_place(algo, &openpgp::crypto::Password::from(password.clone()))
            .expect("decryption failed");
        keys.push(key.into_keypair().unwrap());
    }
    keys
}

#[pyfunction]
#[pyo3(text_signature = "(certdata, data, pin)")]
pub fn sign_bytes_detached_on_card(
    _certdata: Vec<u8>,
    data: Vec<u8>,
    pin: Vec<u8>,
) -> Result<String> {
    let mut result = Vec::new();
    scard::sign_on_card_detached(data.as_slice(), &mut result, pin)?;

    Ok(String::from_utf8(result)?)
}

#[pyfunction]
#[pyo3(text_signature = "(certdata, filepath, pin)")]
pub fn sign_file_detached_on_card(
    _certdata: Vec<u8>,
    filepath: Vec<u8>,
    pin: Vec<u8>,
) -> Result<String> {
    let file = Path::new(str::from_utf8(&filepath[..])?);
    let input = File::open(file)?;

    let mut result = Vec::new();
    scard::sign_on_card_detached(input, &mut result, pin)?;

    Ok(String::from_utf8(result)?)
}

#[pyfunction]
#[pyo3(text_signature = "(certdata, othercertdata, sig_type, uids, password, oncard)")]
fn certify_key(
    py: Python,
    certdata: Vec<u8>,
    othercertdata: Vec<u8>,
    sig_type: u8,
    uids: Vec<String>,
    password: Vec<u8>,
    oncard: bool,
) -> Result<PyObject> {
    let policy = &P::new();

    let cert = openpgp::Cert::from_bytes(&certdata)?;
    let othercert = openpgp::Cert::from_bytes(&othercertdata)?;

    let stype = match sig_type {
        1 => SignatureType::PersonaCertification,
        2 => SignatureType::CasualCertification,
        3 => SignatureType::PositiveCertification,
        _ => SignatureType::GenericCertification,
    };

    let mut keys = Vec::new();

    // Owned OpenPGP card, if applicable
    let mut card_open: Option<Card<Open>> = if oncard {
        Some(scard::first_pcsc_card()?)
    } else {
        None // We're not using a card
    };

    let disk_signer = if !oncard {
        for key in cert
            .keys()
            .with_policy(policy, None)
            .alive()
            .revoked(false)
            .for_certification()
            .secret()
            .map(|kd| kd.key())
        {
            let mut key = key.clone();
            let algo = key.pk_algo();

            key.secret_mut()
                .decrypt_in_place(algo, &openpgp::crypto::Password::from(password.clone()))
                .expect("decryption failed");
            keys.push(key.into_keypair().unwrap());
        }
        if keys.is_empty() {
            return Err(JceError::new(
                "No key is available for certification.".to_string(),
            ));
        }
        // Now we know for sure that there is a key
        let key = keys
            .first()
            .expect("We must have a certification key by now");

        Some(key.clone())
    } else {
        None
    };

    // To store the signatures till we insert them
    let mut new_certificates: Vec<Signature> = Vec::new();
    // Now let us find each of given user id values in the given key.
    for uid in othercert.userids() {
        if let Ok(userid_value) = std::str::from_utf8(uid.userid().value()) {
            // Now loop over the given user id values as input
            for userid in &uids {
                if userid_value == userid {
                    let u = uid.userid();
                    // Now certify
                    let sig = match oncard {
                        true => {
                            let card = card_open.as_mut().unwrap();
                            let mut tx = card.transaction()?;
                            tx.verify_user_for_signing(&password)?;

                            let mut sign = tx.signing_card().ok_or(JceError::new(
                                "Failed to switch card to Sign mode".to_string(),
                            ))?;

                            let mut card_signer =
                                sign.signer(&|| println!("Touch confirmation needed for signing"))?;

                            u.certify(&mut card_signer, &othercert, stype, None, None)?
                        }
                        false => {
                            let mut signer = disk_signer.as_ref().unwrap().clone();
                            u.certify(&mut signer, &othercert, stype, None, None)?
                        }
                    };
                    new_certificates.push(sig);
                };
            }
        }
    }

    // Now let us to put the signatures back
    let finalsig = othercert.insert_packets(new_certificates)?;
    // Now let us return the secret key as Python Bytes
    let mut buf = Vec::new();
    let mut buffer = Vec::new();

    let mut writer = Writer::new(&mut buf, Kind::PublicKey)?;
    finalsig.as_tsk().serialize(&mut buffer)?;
    writer.write_all(&buffer)?;
    writer.finalize()?;

    // Let us return the cert data which can be saved in the database
    let res = PyBytes::new(py, &buf);
    Ok(res.into())
}

#[pyfunction]
#[pyo3(text_signature = "(certdata, filepath, output, pin)")]
pub fn sign_file_on_card(
    _certdata: Vec<u8>,
    filepath: Vec<u8>,
    output: Vec<u8>,
    pin: Vec<u8>,
    cleartext: bool,
) -> Result<bool> {
    let file = Path::new(str::from_utf8(&filepath[..])?);
    let mut input = File::open(file)?;
    let mut outfile = File::create(str::from_utf8(&output[..])?)?;

    scard::sign_on_card(&mut input, &mut outfile, pin, cleartext)?;

    Ok(true)
}

#[pyfunction]
#[pyo3(text_signature = "(certdata, data, pin)")]
pub fn sign_bytes_on_card(
    _certdata: Vec<u8>,
    data: Vec<u8>,
    pin: Vec<u8>,
    cleartext: bool,
) -> Result<Vec<u8>> {
    let mut result = Vec::new();

    scard::sign_on_card(data.as_slice(), &mut result, pin, cleartext)?;

    Ok(result)
}

fn sign_file_internal(
    cert: &openpgp::cert::Cert,
    input: &mut dyn io::Read,
    output: &mut (dyn io::Write + Send + Sync),
    password: String,
    cleartext: bool,
) -> Result<bool> {
    // TODO: WHY?
    let mut input = input;

    let mut keys = get_keys(cert, password);

    if keys.is_empty() {
        return Err(JceError::new("No signing key is present.".to_string()));
    }

    let mut sink = Message::new(output);

    // Stream an OpenPGP message.
    let mut message = Message::new(&mut sink);
    if !cleartext {
        message = Armorer::new(message).build()?;
    };

    let builder = match cleartext {
        false => SignatureBuilder::new(SignatureType::Binary),
        true => SignatureBuilder::new(SignatureType::Text),
    };
    // Now, create a signer with the builder.
    let mut signer =
        Signer::with_template(message, keys.pop().expect("No key for signing"), builder);

    // Now if we need cleartext signature
    if cleartext {
        signer = signer.cleartext();
    }

    for s in keys {
        signer = signer.add_signer(s);
    }

    // Emit a literal data packet or direct writer for cleartext.
    let mut writer = match cleartext {
        false => LiteralWriter::new(signer.build()?).build()?,
        true => signer.build()?,
    };

    // Copy all the data.
    io::copy(&mut input, &mut writer).expect("Failed to sign data");

    // Finally, teardown the stack to ensure all the data is written.
    // signer.finalize().expect("Failed to write data");
    writer.finalize()?;

    sink.finalize()?;
    Ok(true)
}

fn sign_bytes_internal(
    py: Python,
    cert: &openpgp::cert::Cert,
    input: &mut dyn io::Read,
    password: String,
    cleartext: bool,
) -> Result<PyObject> {
    // TODO: WHY?
    let mut input = input;

    let mut keys = get_keys(cert, password);

    if keys.is_empty() {
        return Err(JceError::new("No signing key is present.".to_string()));
    }

    let mut result = Vec::new();
    let mut sink = Message::new(&mut result);

    // Stream an OpenPGP message.
    let mut message = Message::new(&mut sink);
    if !cleartext {
        message = Armorer::new(message).build()?;
    };

    let builder = match cleartext {
        false => SignatureBuilder::new(SignatureType::Binary),
        true => SignatureBuilder::new(SignatureType::Text),
    };
    // Now, create a signer with the builder.
    let mut signer =
        Signer::with_template(message, keys.pop().expect("No key for signing"), builder);

    // Now if we need cleartext signature
    if cleartext {
        signer = signer.cleartext();
    }

    for s in keys {
        signer = signer.add_signer(s);
    }

    // Emit a literal data packet or direct writer for cleartext.
    let mut writer = match cleartext {
        false => LiteralWriter::new(signer.build()?).build()?,
        true => signer.build()?,
    };

    // Copy all the data.
    io::copy(&mut input, &mut writer).expect("Failed to sign data");

    // Finally, teardown the stack to ensure all the data is written.
    // signer.finalize().expect("Failed to write data");
    writer.finalize()?;

    sink.finalize()?;

    // Let us return the cert data which can be saved in the database
    let res = PyBytes::new(py, &result);
    Ok(res.into())
}

fn sign_bytes_detached_internal(
    cert: &openpgp::cert::Cert,
    input: &mut dyn io::Read,
    password: String,
) -> Result<String> {
    // TODO: WHY?
    let mut input = input;

    let mut keys = get_keys(cert, password);

    if keys.is_empty() {
        return Err(JceError::new("No signing key is present.".to_string()));
    }

    let mut result = Vec::new();
    let mut sink = armor::Writer::new(&mut result, armor::Kind::Signature)
        .expect("Failed to create armored writer.");

    // Stream an OpenPGP message.
    let message = Message::new(&mut sink);

    // Now, create a signer that emits the detached signature(s).
    let mut signer = Signer::new(message, keys.pop().expect("No key for signing"));
    for s in keys {
        signer = signer.add_signer(s);
    }
    let mut signer = signer.detached().build().expect("Failed to create signer");

    // Copy all the data.
    io::copy(&mut input, &mut signer).expect("Failed to sign data");

    // Finally, teardown the stack to ensure all the data is written.
    signer.finalize().expect("Failed to write data");

    // Finalize the armor writer.
    sink.finalize().expect("Failed to write data");

    Ok(String::from_utf8(result)?)
}

#[pyfunction]
#[pyo3(text_signature = "(certdata, newcertdata, force)")]
fn merge_keys(
    _py: Python,
    certdata: Vec<u8>,
    newcertdata: Vec<u8>,
    force: bool,
) -> Result<PyObject> {
    let cert = openpgp::Cert::from_bytes(&certdata)?;
    let newcert = openpgp::Cert::from_bytes(&newcertdata)?;
    if cert.as_tsk() == newcert.as_tsk() && !force {
        return Err(JceError::new(
            "Both keys are same. Can not merge.".to_string(),
        ));
    }
    // Now let us merge the new one into old one.
    // Remember, the opposite is a security risk.
    let mergred_cert = cert.merge_public_and_secret(newcert)?;
    let cert_packets = mergred_cert.armored().to_vec()?;
    let res = PyBytes::new(_py, &cert_packets);
    Ok(res.into())
}

/// This function takes a path to an encrypted message and tries to guess the keyids it was
/// encrypted for. Note: It will read through the whole file and not memory happy code. Use with
/// care.
#[pyfunction]
#[pyo3(text_signature = "(filepath)")]
fn file_encrypted_for(_py: Python, filepath: String) -> Result<PyObject> {
    let mut ppr = PacketParser::from_file(filepath)?;
    let plist = PyList::empty(_py);
    while let PacketParserResult::Some(pp) = ppr {
        // Get the packet out of the parser and start parsing the next
        // packet, recursing.
        let (packet, next_ppr) = pp.recurse()?;
        ppr = next_ppr;

        if let Packet::PKESK(ps) = packet {
            let id = ps.recipient().to_hex();
            plist.append(id)?;
        }
    }
    Ok(plist.into())
}

/// This function takes an encrypted message as bytes and tries to guess the keyids it was
/// encrypted for. Note: It will keep the whole content on memory and not memory happy code. Use
/// with care.
#[pyfunction]
#[pyo3(text_signature = "(messagedata)")]
fn bytes_encrypted_for(_py: Python, messagedata: Vec<u8>) -> Result<PyObject> {
    let mut ppr = PacketParser::from_bytes(&messagedata[..])?;
    let plist = PyList::empty(_py);
    while let PacketParserResult::Some(pp) = ppr {
        // Get the packet out of the parser and start parsing the next
        // packet, recursing.
        let (packet, next_ppr) = pp.recurse()?;
        ppr = next_ppr;

        if let Packet::PKESK(ps) = packet {
            let id = ps.recipient().to_hex();
            plist.append(id)?;
        }
    }
    Ok(plist.into())
}

#[pyfunction]
#[pyo3(text_signature = "(certdata)")]
fn get_pub_key(_py: Python, certdata: Vec<u8>) -> Result<String> {
    let cert = openpgp::Cert::from_bytes(&certdata)?;
    let armored = cert.armored().to_vec()?;
    Ok(String::from_utf8(armored)?)
}

#[pyfunction]
#[pyo3(text_signature = "(certdata, pin, password, whichslot)")]
fn upload_primary_to_smartcard(
    _py: Python,
    certdata: Vec<u8>,
    pin: Vec<u8>,
    password: String,
    whichslot: u8,
) -> Result<bool> {
    let cert = openpgp::Cert::from_bytes(&certdata)?;

    // whichslot, 2 for signing, 4 for authentication
    // Can be either of this.

    // Here the key slot is something I decided
    // 2 -- singing slot on the key
    // 3 -- authentication slot on the key
    let mut result = false;

    if (whichslot & 0x02) == 0x02 {
        result = scard::parse_and_move_a_key(cert, 2, pin, password, true)?;
    } else if (whichslot & 0x04) == 0x04 {
        result = scard::parse_and_move_a_key(cert, 3, pin, password, true)?;
    }
    Ok(result)
}

#[pyfunction]
#[pyo3(text_signature = "(certdata, pin, password, whichkeys)")]
fn upload_to_smartcard(
    _py: Python,
    certdata: Vec<u8>,
    pin: Vec<u8>,
    password: String,
    whichkeys: u8,
) -> Result<bool> {
    let cert = openpgp::Cert::from_bytes(&certdata)?;

    // whichkeys, 1 for encryption, 2 for signing, 4 for authentication
    // 3 - both enc and signing
    // 5 - both enc and authentication.
    // 6 - both signing and authentication
    // 7 - all three subkeys
    //

    // Here the keytype is something I decided
    // 1 -- encryption key
    // 2 -- singing key
    // 3 -- authentication key
    let mut result = false;
    if (whichkeys & 0x01) == 0x01 {
        result =
            scard::parse_and_move_a_key(cert.clone(), 1, pin.clone(), password.clone(), false)?;
    }

    if (whichkeys & 0x02) == 0x02 {
        result =
            scard::parse_and_move_a_key(cert.clone(), 2, pin.clone(), password.clone(), false)?;
    }
    if (whichkeys & 0x04) == 0x04 {
        result = scard::parse_and_move_a_key(cert, 3, pin, password, false)?;
    }
    Ok(result)
}

#[pyfunction]
#[pyo3(text_signature = "(certdata)")]
fn get_signing_pubkey(py: Python, certdata: Vec<u8>) -> Result<PyObject> {
    // Note: For now we will return the first signing key (maybe the primary key).
    use std::fmt::Write;
    let pd = PyDict::new(py);
    let cert = openpgp::Cert::from_bytes(&certdata)?;

    let policy = P::new();
    let mut valid_ka = cert
        .keys()
        .with_policy(&policy, None)
        .alive()
        .revoked(false)
        .for_signing();
    if let Some(ka) = valid_ka.next() {
        // First let us get the value of e from the public key
        let public = ka.parts_as_public();
        match public.mpis().clone() {
            openpgp::crypto::mpi::PublicKey::RSA { ref e, ref n } => {
                let mut result_n = String::new();
                let internal = n.value().to_vec();
                for v in internal.iter() {
                    write!(&mut result_n, "{:02X}", v)?;
                }
                let mut result_e = String::new();
                let internal = e.value().to_vec();
                for v in internal.iter() {
                    write!(&mut result_e, "{:02X}", v)?;
                }
                pd.set_item("key_type", "RSA")?;
                pd.set_item("n", result_n)?;
                pd.set_item("e", result_e)?;
                return Ok(pd.into());
            }
            _ => {
                return Err(JceError::new("Not yet implemented".to_string()));
            }
        };
    }

    Err(JceError::new("Could not find signing key.".to_string()))
}

#[pyfunction]
#[pyo3(text_signature = "(certdata, comment)")]
fn get_ssh_pubkey(_py: Python, certdata: Vec<u8>, comment: Option<String>) -> Result<String> {
    let cert = openpgp::Cert::from_bytes(&certdata)?;

    let policy = P::new();
    let mut valid_ka = cert
        .keys()
        .subkeys()
        .with_policy(&policy, None)
        .alive()
        .revoked(false)
        .for_authentication();
    if let Some(ka) = valid_ka.next() {
        // First let us get the value of e from the public key
        let public = ka.parts_as_public();
        let (key_type, kind) = match public.mpis().clone() {
            openpgp::crypto::mpi::PublicKey::RSA { ref e, ref n } => {
                let key = sshkeys::RsaPublicKey {
                    e: e.value().to_vec(),
                    n: n.value().to_vec(),
                };
                let key_type = sshkeys::KeyType::from_name("ssh-rsa").unwrap();
                let kind = sshkeys::PublicKeyKind::Rsa(key);
                (key_type, kind)
            }
            openpgp::crypto::mpi::PublicKey::ECDSA { curve, q, .. } => {
                let (ssh_curve, name) = match curve {
                    openpgp::types::Curve::NistP256 => (
                        sshkeys::Curve::from_identifier("nistp256").unwrap(),
                        "ecdsa-sha2-nistp256",
                    ),
                    openpgp::types::Curve::NistP384 => (
                        sshkeys::Curve::from_identifier("nistp384").unwrap(),
                        "ecdsa-sha2-nistp384",
                    ),
                    openpgp::types::Curve::NistP521 => (
                        sshkeys::Curve::from_identifier("nistp521").unwrap(),
                        "ecdsa-sha2-nistp521",
                    ),
                    _ => {
                        return Err(JceError::new("Unknown ECDSA curve for us.".to_string()));
                    }
                };
                let key_type = sshkeys::KeyType::from_name(name).unwrap();
                let kind = sshkeys::PublicKeyKind::Ecdsa(sshkeys::EcdsaPublicKey {
                    curve: ssh_curve,
                    key: q.value().to_vec(),
                    sk_application: None,
                });
                (key_type, kind)
            }
            openpgp::crypto::mpi::PublicKey::EdDSA { curve: _, q } => {
                let key_type = sshkeys::KeyType::from_name("ssh-ed25519").unwrap();
                let kind = sshkeys::PublicKeyKind::Ed25519(sshkeys::Ed25519PublicKey {
                    key: q.value().to_vec(),
                    sk_application: None,
                });
                (key_type, kind)
            }
            _ => {
                return Err(JceError::new("Unknown Public Key.".to_string()));
            }
        };
        let public_key = sshkeys::PublicKey {
            key_type,
            kind,
            comment,
        };
        let mut keydata = vec![];
        public_key.write(&mut keydata)?;

        let s = String::from_utf8_lossy(&keydata).to_string();
        return Ok(s);
    }

    Err(JceError::new(
        "Could not find authentication subkey for ssh.".to_string(),
    ))
}

/// Parses the given file path, and returns a tuple with various data.
///
/// - The first item is a list of user ids as dictionary.
///    [{"value": xxx, "comment": "xxx", "email": "xxx", "uri": "xxx", "revoked": boolean}, ]
/// - Second item is the `fingerprint` as string.
/// - Boolean  to mark if secret key or public
/// - expirationtime as datetime.datetime
/// - creationtime as datetime.datetime
/// - othervalues is another dictionary, inside of it.
///   - "subkeys": [("subkey keyid as hex", "fingerprint as hex", creationtime, expirationtime,
///                "keytype", "revoked as boolean")]. The subkey type can be of "encryption", "signing",
///                "authentication", or "unknown".
///   - "keyid": "primary key id in hex"
#[pyfunction]
#[pyo3(text_signature = "(certpath)")]
fn parse_cert_file(
    py: Python,
    certpath: String,
) -> Result<(PyObject, String, bool, PyObject, PyObject, PyObject)> {
    let cert = openpgp::Cert::from_file(certpath)?;
    internal_parse_cert(py, cert)
}

/// Parses the given bytes, and returns a tuple with various data.
///
/// - The first item is a list of user ids as dictionary.
///    [{"value": xxx, "comment": "xxx", "email": "xxx", "uri": "xxx", "revoked": boolean}, ]
/// - Second item is the `fingerprint` as string.
/// - Boolean  to mark if secret key or public
/// - expirationtime as datetime.datetime
/// - creationtime as datetime.datetime
/// - othervalues is another dictionary, inside of it.
///   - "subkeys": [("subkey keyid as hex", "fingerprint as hex", creationtime, expirationtime,
///                "keytype", "revoked as boolean")]. The subkey type can be of "encryption", "signing",
///                "authentication", or "unknown".
///   - "keyid": "primary key id in hex"
#[pyfunction]
#[pyo3(text_signature = "(certpath)")]
fn parse_cert_bytes(
    py: Python,
    certdata: Vec<u8>,
) -> Result<(PyObject, String, bool, PyObject, PyObject, PyObject)> {
    let cert = openpgp::Cert::from_bytes(&certdata)?;
    internal_parse_cert(py, cert)
}

fn internal_parse_cert(
    py: Python,
    cert: openpgp::Cert,
) -> Result<(PyObject, String, bool, PyObject, PyObject, PyObject)> {
    let p = P::new();
    let creationtime = match cert.primary_key().with_policy(&p, None) {
        Ok(value) => {
            let ctime = value.creation_time();
            let dt: DateTime<Utc> = DateTime::from(ctime);
            Some(PyDateTime::from_timestamp(py, dt.timestamp() as f64, None)?)
        }
        _ => None,
    };

    let expirationtime = match cert.primary_key().with_policy(&p, None) {
        Ok(value) => match value.key_expiration_time() {
            Some(etime) => {
                let dt: DateTime<Utc> = DateTime::from(etime);
                Some(PyDateTime::from_timestamp(py, dt.timestamp() as f64, None)?)
            }
            _ => None,
        },
        Err(txt) => {
            let mut err_msg = Vec::new();
            let eiters = txt.chain();
            for error in eiters {
                err_msg.push(error.to_string());
            }
            return Err(JceError::new(err_msg.join(", ")));
        }
    };
    let plist = PyList::empty(py);
    for ua in cert.userids() {
        let pd = PyDict::new(py);
        //println!("  {}", String::from_utf8_lossy(ua.value()));
        pd.set_item("value", String::from_utf8_lossy(ua.value()))?;
        // If we have a name part in the UID
        if let Ok(Some(name)) = ua.name() {
            pd.set_item("name", name)?;
        }

        // If we have a comment part in the UID
        if let Ok(Some(comment)) = ua.comment() {
            pd.set_item("comment", comment)?;
        }

        // If we have a email part in the UID
        if let Ok(Some(email)) = ua.email() {
            pd.set_item("email", email)?;
        }

        // If we have a URI part in the UID
        if let Ok(Some(uri)) = ua.uri() {
            pd.set_item("uri", uri)?;
        }
        let mut revoked = false;
        // Based on https://docs.sequoia-pgp.org/1.0.0/sequoia_openpgp/cert/struct.UserIDRevocationBuilder.html#examples
        if let RevocationStatus::Revoked(_) = ua.revocation_status(&p, None) {
            revoked = true;
        };
        pd.set_item("revoked", revoked)?;

        // This list contains a list of dictionary
        let certification_list = PyList::empty(py);
        // Now we will deal with the certifications, that is if anyone else signed this UID.
        for c in ua.certifications() {
            // This is the type of certification
            let c_type = match c.typ() {
                SignatureType::GenericCertification => "generic",
                SignatureType::CasualCertification => "casual",
                SignatureType::PersonaCertification => "persona",
                SignatureType::PositiveCertification => "postive",
                _ => "unknown",
            };

            let creationtime = {
                let sct = c.signature_creation_time();
                match sct {
                    Some(sct_value) => {
                        let dt: DateTime<Utc> = DateTime::from(sct_value);
                        Some(PyDateTime::from_timestamp(py, dt.timestamp() as f64, None)?)
                    }
                    None => None,
                }
            };

            // Now we need a list of issuers for this certification
            //
            let issuer_list = PyList::empty(py);
            for issuer in c.get_issuers() {
                //let fp_keyid = PyTuple::new(py, &[issuer.])
                match issuer {
                    KeyHandle::Fingerprint(finger) => issuer_list.append(PyTuple::new(
                        py,
                        &["fingerprint".to_string(), finger.to_hex()],
                    ))?,
                    KeyHandle::KeyID(kid) => issuer_list
                        .append(PyTuple::new(py, &["keyid".to_string(), kid.to_hex()]))?,
                }
            }

            // Now add this one certification
            let ud_dict = PyDict::new(py);
            ud_dict.set_item("certification_type", c_type)?;
            ud_dict.set_item("certification_list", issuer_list)?;
            ud_dict.set_item("creationtime", creationtime)?;

            certification_list.append(ud_dict)?;
        }

        // Now let us set the certifications for this user id
        pd.set_item("certifications", certification_list)?;

        plist.append(pd)?;
    }

    let subkeys = PyList::empty(py);
    for ka in cert.keys().with_policy(&p, None).subkeys() {
        let expirationtime = match ka.key_expiration_time() {
            Some(etime) => {
                let dt: DateTime<Utc> = DateTime::from(etime);
                Some(PyDateTime::from_timestamp(py, dt.timestamp() as f64, None)?)
            }
            _ => None,
        };

        let creationtime = {
            let dt: DateTime<Utc> = DateTime::from(ka.creation_time());
            Some(PyDateTime::from_timestamp(py, dt.timestamp() as f64, None)?)
        };

        // To find what kind of subkey is this.
        let keytype = if ka.for_storage_encryption() | ka.for_transport_encryption() {
            String::from("encryption")
        } else if ka.for_signing() {
            String::from("signing")
        } else if ka.for_authentication() {
            String::from("authentication")
        } else {
            String::from("unknown")
        };

        // To check if it is revoked or not
        // Just the oppostie from the filter values in
        // https://docs.sequoia-pgp.org/1.0.0/sequoia_openpgp/cert/amalgamation/struct.ValidComponentAmalgamationIter.html#method.revoked
        let revoked = match ka.revocation_status() {
            RevocationStatus::Revoked(_) => true,
            RevocationStatus::CouldBe(_) => false,
            RevocationStatus::NotAsFarAsWeKnow => false,
        };
        subkeys.append((
            ka.keyid().to_hex(),
            ka.fingerprint().to_hex(),
            creationtime,
            expirationtime,
            keytype,
            revoked,
        ))?;
    }

    // To find out if the primary key can sign or not.
    let can_primary_sign = match cert.primary_key().with_policy(&p, None) {
        Ok(pkey) => pkey.for_signing(),
        _ => false,
    };

    let othervalues = PyDict::new(py);
    othervalues.set_item("keyid", cert.primary_key().keyid().to_hex())?;
    othervalues.set_item("subkeys", subkeys)?;
    othervalues.set_item("can_primary_sign", can_primary_sign)?;

    Ok((
        plist.into(),
        cert.fingerprint().to_hex(),
        cert.is_tsk(),
        expirationtime.to_object(py),
        creationtime.to_object(py),
        othervalues.to_object(py),
    ))
}

/// This function takes a password and an userid as strings, returns a tuple of public and private
/// key and the fingerprint in hex. Remember to save the keys for future use.
#[pyfunction]
#[pyo3(
    text_signature = "(password, userid, cipher, creation, expiration, subkeys_expiration, whichkeys, can_primary_sign, can_primary_expire)"
)]
#[allow(clippy::too_many_arguments)]
fn create_key(
    password: String,
    userids: Vec<String>,
    cipher: String,
    creation: i64,
    expiration: i64,
    subkeys_expiration: bool,
    whichkeys: u8,
    can_primary_sign: bool,
    can_primary_expire: bool,
) -> Result<(String, String, String)> {
    let mut cdt: Option<DateTime<Utc>> = None;
    // Default we create RSA4k keys
    let mut ciphervalue = CipherSuite::RSA4k;
    if cipher == *"RSA2k" {
        ciphervalue = CipherSuite::RSA2k;
    } else if cipher == *"Cv25519" {
        ciphervalue = CipherSuite::Cv25519;
    }

    let mut crtbuilder = CertBuilder::new()
        .set_cipher_suite(ciphervalue)
        .set_password(Some(openpgp::crypto::Password::from(password)));

    for uid in userids {
        crtbuilder = crtbuilder.add_userid(uid);
    }

    // To mark if our primary key needs to have signing capability
    let crtbuilder = match can_primary_sign {
        true => {
            crtbuilder.set_primary_key_flags(KeyFlags::empty().set_signing().set_certification())
        }
        false => crtbuilder,
    };

    let crtbuilder = match creation {
        0 => crtbuilder,
        _ => {
            cdt = Some(DateTime::<Utc>::from_naive_utc_and_offset(
                NaiveDateTime::from_timestamp_opt(creation, 0).unwrap(),
                Utc,
            ));
            crtbuilder.set_creation_time(SystemTime::from(cdt.unwrap()))
        }
    };

    let crtbuilder = match expiration {
        0 => {
            let crtbuilder = if (whichkeys & 0x01) == 0x01 {
                crtbuilder.add_subkey(
                    KeyFlags::empty()
                        .set_storage_encryption()
                        .set_transport_encryption(),
                    None,
                    None,
                )
            } else {
                crtbuilder
            };
            let crtbuilder = if (whichkeys & 0x02) == 0x02 {
                crtbuilder.add_signing_subkey()
            } else {
                crtbuilder
            };
            let crtbuilder = if (whichkeys & 0x04) == 0x04 {
                crtbuilder.add_authentication_subkey()
            } else {
                crtbuilder
            };
            crtbuilder
        }

        // Let us calculate the creation time we used
        _ => {
            let validity = match cdt {
                Some(cdt) => Duration::new(expiration as u64 - cdt.timestamp() as u64, 0),

                None => Duration::new(
                    expiration as u64
                        - SystemTime::now()
                            .duration_since(UNIX_EPOCH)
                            .unwrap()
                            .as_secs(),
                    0,
                ),
            };
            let crtbuilder = if can_primary_expire {
                crtbuilder.set_validity_period(validity)
            } else {
                crtbuilder
            };
            if subkeys_expiration {
                let crtbuilder = if (whichkeys & 0x01) == 0x01 {
                    crtbuilder.add_subkey(
                        KeyFlags::empty()
                            .set_storage_encryption()
                            .set_transport_encryption(),
                        validity,
                        None,
                    )
                } else {
                    crtbuilder
                };
                let crtbuilder = if (whichkeys & 0x02) == 0x02 {
                    crtbuilder.add_subkey(KeyFlags::empty().set_signing(), validity, None)
                } else {
                    crtbuilder
                };

                let crtbuilder = if (whichkeys & 0x04) == 0x04 {
                    crtbuilder.add_subkey(KeyFlags::empty().set_authentication(), validity, None)
                } else {
                    crtbuilder
                };
                crtbuilder
            } else {
                crtbuilder
            }
        }
    };

    let (cert, _) = crtbuilder.generate()?;

    let mut buf = Vec::new();
    let mut buffer = Vec::new();

    let mut writer = Writer::new(&mut buf, Kind::SecretKey)?;
    cert.as_tsk().serialize(&mut buffer)?;
    writer.write_all(&buffer)?;
    writer.finalize()?;
    let armored = cert.armored().to_vec()?;
    Ok((
        String::from_utf8(armored)?,
        String::from_utf8(buf)?,
        cert.fingerprint().to_hex(),
    ))
}

/// This function takes a list of public key paths, and encrypts the given data from the opened
/// filehandler in bytes to an output file. You can also pass boolen flag armor for armored output.
/// Always remember to open the file in the Python side in "rb" mode, so that the `read()` call can
/// return bytes.
#[pyfunction]
#[pyo3(text_signature = "(publickeys, fh, output, armor=False)")]
fn encrypt_filehandler_to_file(
    _py: Python,
    publickeys: Vec<Vec<u8>>,
    fh: PyObject,
    output: Vec<u8>,
    armor: Option<bool>,
) -> Result<bool> {
    let data = fh.call_method(_py, "read", (), None)?;
    let pbytes: &PyBytes = data
        .as_ref(_py)
        .downcast::<PyBytes>()
        .expect("Excepted bytes");
    let filedata: Vec<u8> = Vec::from(pbytes.as_bytes());
    encrypt_bytes_to_file(publickeys, filedata, output, armor)
}

/// This function takes a list of public key paths, and encrypts the given data in bytes to an output
/// file. You can also pass boolen flag armor for armored output.
#[pyfunction]
#[pyo3(text_signature = "(publickeys, data, output, armor=False)")]
fn encrypt_bytes_to_file(
    publickeys: Vec<Vec<u8>>,
    data: Vec<u8>,
    output: Vec<u8>,
    armor: Option<bool>,
) -> Result<bool> {
    let mut certs = Vec::new();
    for certdata in publickeys {
        certs.push(openpgp::Cert::from_bytes(&certdata)?);
    }
    let mode = KeyFlags::empty().set_storage_encryption();

    let p = P::new();
    let recipients = certs.iter().flat_map(|cert| {
        cert.keys()
            .with_policy(&p, None)
            .alive()
            .revoked(false)
            .key_flags(&mode)
    });
    let mut outfile = File::create(str::from_utf8(&output[..])?)?;
    // TODO: Find better ways to write this code
    match armor {
        // For armored output file.
        Some(true) => {
            let mut sink = armor::Writer::new(&mut outfile, armor::Kind::Message).unwrap();
            // Stream an OpenPGP message.
            let message = Message::new(&mut sink);

            // We want to encrypt a literal data packet.
            let encryptor = match Encryptor::for_recipients(message, recipients).build() {
                Ok(value) => value,
                Err(_) => {
                    return Err(JceError::new("Can not encrypt.".to_string()));
                }
            };

            let mut literal_writer = LiteralWriter::new(encryptor)
                .build()
                .expect("Failed to create literal writer");

            // Copy data to our writer stack to encrypt the data.
            literal_writer.write_all(&data)?;

            // Finally, finalize the OpenPGP message by tearing down the
            // writer stack.
            literal_writer.finalize()?;

            // Finalize the armor writer.
            sink.finalize().expect("Failed to write data");
        }
        _ => {
            let message = Message::new(&mut outfile);

            // We want to encrypt a literal data packet.
            let encryptor = Encryptor::for_recipients(message, recipients)
                .build()
                .expect("Failed to create encryptor");

            let mut literal_writer = LiteralWriter::new(encryptor)
                .build()
                .expect("Failed to create literal writer");

            // Copy data to our writer stack to encrypt the data.
            literal_writer.write_all(&data).unwrap();

            // Finally, finalize the OpenPGP message by tearing down the
            // writer stack.
            literal_writer.finalize()?;
        }
    }

    Ok(true)
}

/// This function takes a list of public key paths, and encrypts the given filepath to an output
/// file. You can also pass boolen flag armor for armored output.
#[pyfunction]
#[pyo3(text_signature = "(publickeys, filepath, output, armor=False)")]
fn encrypt_file_internal(
    publickeys: Vec<Vec<u8>>,
    filepath: Vec<u8>,
    output: Vec<u8>,
    armor: Option<bool>,
) -> Result<bool> {
    let mut certs = Vec::new();
    for certdata in publickeys {
        certs.push(openpgp::Cert::from_bytes(&certdata)?);
    }

    let mode = KeyFlags::empty().set_storage_encryption();

    let p = &P::new();
    let recipients = certs.iter().flat_map(|cert| {
        cert.keys()
            .with_policy(p, None)
            .alive()
            .revoked(false)
            .key_flags(&mode)
    });

    let mut input = File::open(str::from_utf8(&filepath[..])?)?;
    let mut outfile = File::create(str::from_utf8(&output[..])?)?;
    // TODO: Find better ways to write this code
    match armor {
        // For armored output file.
        Some(true) => {
            let mut sink = armor::Writer::new(&mut outfile, armor::Kind::Message)?;
            // Stream an OpenPGP message.
            let message = Message::new(&mut sink);

            // We want to encrypt a literal data packet.
            let encryptor = Encryptor::for_recipients(message, recipients)
                .build()
                .expect("Failed to create encryptor");

            let mut literal_writer = LiteralWriter::new(encryptor)
                .build()
                .expect("Failed to create literal writer");

            // Copy stdin to our writer stack to encrypt the data.
            io::copy(&mut input, &mut literal_writer).expect("Failed to encrypt");
            //literal_writer.write_all(&data).unwrap();

            // Finally, finalize the OpenPGP message by tearing down the
            // writer stack.
            literal_writer.finalize()?;

            // Finalize the armor writer.
            sink.finalize().expect("Failed to write data");
        }
        _ => {
            let message = Message::new(&mut outfile);

            // We want to encrypt a literal data packet.
            let encryptor = Encryptor::for_recipients(message, recipients)
                .build()
                .expect("Failed to create encryptor");

            let mut literal_writer = LiteralWriter::new(encryptor)
                .build()
                .expect("Failed to create literal writer");

            // Copy stdin to our writer stack to encrypt the data.
            io::copy(&mut input, &mut literal_writer).expect("Failed to encrypt");
            //literal_writer.write_all(&data).unwrap();

            // Finally, finalize the OpenPGP message by tearing down the
            // writer stack.
            literal_writer.finalize()?;
        }
    }

    Ok(true)
}

/// This function takes a list of public key paths, and encrypts the given data in bytes and returns it.
/// You can also pass boolen flag armor for armored output.
#[pyfunction]
#[pyo3(text_signature = "(publickeys, data, armor=False)")]
fn encrypt_bytes_to_bytes(
    py: Python,
    publickeys: Vec<Vec<u8>>,
    data: Vec<u8>,
    armor: Option<bool>,
) -> Result<PyObject> {
    let mut certs = Vec::new();
    for certdata in publickeys {
        certs.push(openpgp::Cert::from_bytes(&certdata)?);
    }

    let mode = KeyFlags::empty().set_storage_encryption();

    let p = P::new();
    let recipients = certs.iter().flat_map(|cert| {
        cert.keys()
            .with_policy(&p, None)
            .alive()
            .revoked(false)
            .key_flags(&mode)
    });
    // TODO: Find better way to do this in rust
    let mut result = Vec::new();
    let mut result2 = Vec::new();
    let mut sink = armor::Writer::new(&mut result2, armor::Kind::Message)?;
    // Stream an OpenPGP message.
    let message = match armor {
        Some(true) => Message::new(&mut sink),
        _ => Message::new(&mut result),
    };
    // We want to encrypt a literal data packet.
    let encryptor = Encryptor::for_recipients(message, recipients)
        .build()
        .expect("Failed to create encryptor");

    let mut literal_writer = LiteralWriter::new(encryptor)
        .build()
        .expect("Failed to create literal writer");

    // Copy stdin to our writer stack to encrypt the data.
    // io::copy(&mut data, &mut literal_writer).expect("Failed to encrypt");
    literal_writer.write_all(&data)?;

    // Finally, finalize the OpenPGP message by tearing down the
    // writer stack.
    literal_writer.finalize()?;

    match armor {
        Some(true) => {
            // Finalize the armor writer.
            sink.finalize().expect("Failed to write data");
            let res = PyBytes::new(py, &result2);
            Ok(res.into())
        }
        _ => {
            let res = PyBytes::new(py, &result);
            Ok(res.into())
        }
    }
}

#[pyclass(module = "johnnycanencrypt")]
#[derive(Debug)]
struct Johnny {
    cert: openpgp::cert::Cert,
}

#[pymethods]
impl Johnny {
    #[new]
    fn new(certdata: Vec<u8>) -> Result<Self> {
        let cert = openpgp::Cert::from_bytes(&certdata)?;
        Ok(Johnny { cert })
    }

    pub fn encrypt_bytes(
        &self,
        py: Python,
        data: Vec<u8>,
        armor: Option<bool>,
    ) -> Result<PyObject> {
        let mode = KeyFlags::empty().set_storage_encryption();
        let p = P::new();
        let recipients = self
            .cert
            .keys()
            .with_policy(&p, None)
            .alive()
            .revoked(false)
            .key_flags(&mode);
        // TODO: Find better way to do this in rust
        let mut result = Vec::new();
        let mut result2 = Vec::new();
        let mut sink = armor::Writer::new(&mut result2, armor::Kind::Message)?;
        // Stream an OpenPGP message.
        let message = match armor {
            Some(true) => Message::new(&mut sink),
            _ => Message::new(&mut result),
        };
        // We want to encrypt a literal data packet.
        let encryptor = Encryptor::for_recipients(message, recipients)
            .build()
            .expect("Failed to create encryptor");

        let mut literal_writer = LiteralWriter::new(encryptor)
            .build()
            .expect("Failed to create literal writer");

        // Copy stdin to our writer stack to encrypt the data.
        // io::copy(&mut data, &mut literal_writer).expect("Failed to encrypt");
        literal_writer.write_all(&data)?;

        // Finally, finalize the OpenPGP message by tearing down the
        // writer stack.
        literal_writer.finalize()?;

        match armor {
            Some(true) => {
                // Finalize the armor writer.
                sink.finalize().expect("Failed to write data");
                let res = PyBytes::new(py, &result2);
                Ok(res.into())
            }
            _ => {
                let res = PyBytes::new(py, &result);
                Ok(res.into())
            }
        }
    }

    pub fn decrypt_bytes(&self, py: Python, data: Vec<u8>, password: String) -> Result<PyObject> {
        let p = P::new();

        let mut result = Vec::new();
        let reader = std::io::BufReader::new(&data[..]);

        let dec = DecryptorBuilder::from_reader(reader);
        let dec2 = match dec {
            Ok(dec) => dec,
            Err(msg) => return Err(JceError::new(format!("Can not create decryptor: {}", msg))),
        };
        let mut decryptor = match dec2.with_policy(&p, None, Helper::new(&p, &self.cert, &password))
        {
            Ok(decr) => decr,
            Err(msg) => return Err(JceError::new(format!("Failed to decrypt: {}", msg))),
        };
        std::io::copy(&mut decryptor, &mut result)?;
        let res = PyBytes::new(py, &result);
        Ok(res.into())
    }
    pub fn encrypt_file(
        &self,
        filepath: Vec<u8>,
        output: Vec<u8>,
        armor: Option<bool>,
    ) -> Result<bool> {
        let mode = KeyFlags::empty().set_storage_encryption();
        let p = &P::new();
        let recipients = self
            .cert
            .keys()
            .with_policy(p, None)
            .alive()
            .revoked(false)
            .key_flags(&mode);
        let mut input = File::open(str::from_utf8(&filepath[..])?)?;
        let mut outfile = File::create(str::from_utf8(&output[..])?)?;
        // TODO: Find better ways to write this code
        match armor {
            // For armored output file.
            Some(true) => {
                let mut sink = armor::Writer::new(&mut outfile, armor::Kind::Message)?;
                // Stream an OpenPGP message.
                let message = Message::new(&mut sink);

                // We want to encrypt a literal data packet.
                let encryptor = Encryptor::for_recipients(message, recipients)
                    .build()
                    .expect("Failed to create encryptor");

                let mut literal_writer = LiteralWriter::new(encryptor)
                    .build()
                    .expect("Failed to create literal writer");

                // Copy stdin to our writer stack to encrypt the data.
                io::copy(&mut input, &mut literal_writer).expect("Failed to encrypt");
                //literal_writer.write_all(&data).unwrap();

                // Finally, finalize the OpenPGP message by tearing down the
                // writer stack.
                literal_writer.finalize()?;

                // Finalize the armor writer.
                sink.finalize().expect("Failed to write data");
            }
            _ => {
                let message = Message::new(&mut outfile);

                // We want to encrypt a literal data packet.
                let encryptor = Encryptor::for_recipients(message, recipients)
                    .build()
                    .expect("Failed to create encryptor");

                let mut literal_writer = LiteralWriter::new(encryptor)
                    .build()
                    .expect("Failed to create literal writer");

                // Copy stdin to our writer stack to encrypt the data.
                io::copy(&mut input, &mut literal_writer).expect("Failed to encrypt");
                //literal_writer.write_all(&data).unwrap();

                // Finally, finalize the OpenPGP message by tearing down the
                // writer stack.
                literal_writer.finalize()?;
            }
        }

        Ok(true)
    }

    pub fn decrypt_file(
        &self,
        filepath: Vec<u8>,
        output: Vec<u8>,
        password: String,
    ) -> Result<bool> {
        let p = P::new();

        let input = File::open(str::from_utf8(&filepath[..])?)?;
        let mut outfile = File::create(str::from_utf8(&output[..])?)?;

        let mut decryptor = DecryptorBuilder::from_reader(input)?.with_policy(
            &p,
            None,
            Helper::new(&p, &self.cert, &password),
        )?;
        std::io::copy(&mut decryptor, &mut outfile)?;
        Ok(true)
    }

    pub fn decrypt_filehandler(
        &self,
        _py: Python,
        fh: PyObject,
        output: Vec<u8>,
        password: String,
    ) -> Result<bool> {
        let p = P::new();

        let filedata = fh.call_method(_py, "read", (), None)?;
        let pbytes: &PyBytes = filedata
            .as_ref(_py)
            .downcast::<PyBytes>()
            .expect("Excepted bytes");
        let data: Vec<u8> = Vec::from(pbytes.as_bytes());

        let reader = std::io::BufReader::new(&data[..]);
        let dec = DecryptorBuilder::from_reader(reader);
        let dec2 = match dec {
            Ok(dec) => dec,
            Err(msg) => return Err(JceError::new(format!("Can not create decryptor: {}", msg))),
        };
        let mut decryptor = match dec2.with_policy(&p, None, Helper::new(&p, &self.cert, &password))
        {
            Ok(decr) => decr,
            Err(msg) => return Err(JceError::new(format!("Failed to decrypt: {}", msg))),
        };

        let mut outfile = File::create(str::from_utf8(&output[..])?)?;

        std::io::copy(&mut decryptor, &mut outfile)?;
        Ok(true)
    }

    pub fn sign_bytes(
        &self,
        py: Python,
        data: Vec<u8>,
        password: String,
        cleartext: bool,
    ) -> Result<PyObject> {
        let mut localdata = io::Cursor::new(data);
        sign_bytes_internal(py, &self.cert, &mut localdata, password, cleartext)
    }

    pub fn sign_file(
        &self,
        inputpath: Vec<u8>,
        output: Vec<u8>,
        password: String,
        cleartext: bool,
    ) -> Result<bool> {
        // This is the file we will sign.
        let file = Path::new(str::from_utf8(&inputpath[..])?);
        let mut localdata = File::open(file)?;
        // This is where the signed message will go
        let mut outfile = File::create(str::from_utf8(&output[..])?)?;
        sign_file_internal(
            &self.cert,
            &mut localdata,
            &mut outfile,
            password,
            cleartext,
        )
    }

    pub fn sign_bytes_detached(&self, data: Vec<u8>, password: String) -> Result<String> {
        let mut localdata = io::Cursor::new(data);
        sign_bytes_detached_internal(&self.cert, &mut localdata, password)
    }

    pub fn sign_file_detached(&self, filepath: Vec<u8>, password: String) -> Result<String> {
        let file = Path::new(str::from_utf8(&filepath[..])?);
        let mut localdata = File::open(file)?;
        sign_bytes_detached_internal(&self.cert, &mut localdata, password)
    }

    pub fn verify_bytes_detached(&self, data: Vec<u8>, sig: Vec<u8>) -> Result<bool> {
        let p = P::new();
        let vh = VHelper::new(&self.cert);
        let mut v = DetachedVerifierBuilder::from_bytes(&sig[..])?.with_policy(&p, None, vh)?;
        match v.verify_bytes(data) {
            Ok(()) => Ok(true),
            Err(_) => Ok(false),
        }
    }

    pub fn verify_file_detached(&self, filepath: Vec<u8>, sig: Vec<u8>) -> Result<bool> {
        let p = P::new();
        let vh = VHelper::new(&self.cert);
        let mut v = DetachedVerifierBuilder::from_bytes(&sig[..])?.with_policy(&p, None, vh)?;
        let path = Path::new(str::from_utf8(&filepath[..])?);
        match v.verify_file(path) {
            Ok(()) => Ok(true),
            Err(_) => Ok(false),
        }
    }

    pub fn verify_bytes(&self, data: Vec<u8>) -> Result<bool> {
        let p = P::new();
        let vh = VHelper::new(&self.cert);
        let mut v = VerifierBuilder::from_bytes(&data[..])?.with_policy(&p, None, vh)?;
        let mut tmp = tempfile::tempfile()?;
        std::io::copy(&mut v, &mut tmp)?;
        Ok(v.message_processed())
    }

    pub fn verify_and_extract_bytes(&self, py: Python<'_>, data: Vec<u8>) -> Result<PyObject> {
        let p = P::new();
        let vh = VHelper::new(&self.cert);
        let mut v = VerifierBuilder::from_bytes(&data[..])?.with_policy(&p, None, vh)?;
        let mut tmp = tempfile::tempfile()?;
        std::io::copy(&mut v, &mut tmp)?;
        tmp.seek(SeekFrom::Start(0))?;
        let mut inside: Vec<u8> = Vec::new();
        let _ = tmp.read_to_end(&mut inside)?;
        let output = PyBytes::new(py, &inside);
        Ok(output.into())
    }

    pub fn verify_file(&self, filepath: Vec<u8>) -> Result<bool> {
        let p = P::new();
        let vh = VHelper::new(&self.cert);
        let path = Path::new(str::from_utf8(&filepath[..])?);
        let mut v = VerifierBuilder::from_file(path)?.with_policy(&p, None, vh)?;
        let mut tmp = tempfile::tempfile()?;
        std::io::copy(&mut v, &mut tmp)?;
        Ok(v.message_processed())
    }

    pub fn verify_and_extract_file(&self, filepath: Vec<u8>, output: Vec<u8>) -> Result<bool> {
        let p = P::new();
        let vh = VHelper::new(&self.cert);
        let path = Path::new(str::from_utf8(&filepath[..])?);
        let mut v = VerifierBuilder::from_file(path)?.with_policy(&p, None, vh)?;
        let mut file = File::create(str::from_utf8(&output[..])?)?;
        std::io::copy(&mut v, &mut file)?;
        Ok(v.message_processed())
    }
}

#[pyfunction]
pub fn is_smartcard_connected() -> PyResult<bool> {
    match scard::is_smartcard_connected() {
        Ok(value) => Ok(value),
        Err(_) => Ok(false),
    }
}

/// Returns a tuple with the firmware version.
#[pyfunction]
pub fn get_card_version(py: Python) -> Result<PyObject> {
    let version = scard::firmware_version_yubico()?;

    let result = PyTuple::new(py, version.iter());
    Ok(result.into())
}

/// TouchMode for Yubikeys
#[pyclass]
#[derive(Clone, Debug)]
pub enum TouchMode {
    Off = 0x00,
    On = 0x01,
    Fixed = 0x02,
    Cached = 0x03,
    CachedFixed = 0x04,
}

impl From<TouchMode> for TouchPolicy {
    fn from(value: TouchMode) -> Self {
        match value {
            TouchMode::Off => TouchPolicy::Off,
            TouchMode::On => TouchPolicy::On,
            TouchMode::Fixed => TouchPolicy::Fixed,
            TouchMode::Cached => TouchPolicy::Cached,
            TouchMode::CachedFixed => TouchPolicy::CachedFixed,
        }
    }
}

impl TryFrom<TouchPolicy> for TouchMode {
    type Error = JceError;

    fn try_from(value: TouchPolicy) -> std::result::Result<Self, Self::Error> {
        match value {
            TouchPolicy::Off => Ok(TouchMode::Off),
            TouchPolicy::On => Ok(TouchMode::On),
            TouchPolicy::Fixed => Ok(TouchMode::Fixed),
            TouchPolicy::Cached => Ok(TouchMode::Cached),
            TouchPolicy::CachedFixed => Ok(TouchMode::CachedFixed),
            _ => Err(JceError::new("Can not parse touch policy.".to_string())),
        }
    }
}

#[pyclass]
#[derive(Clone, Debug)]
pub enum KeySlot {
    Signature,
    Encryption,
    Authentication,
    Attestation,
}

impl From<KeySlot> for KeyType {
    fn from(value: KeySlot) -> Self {
        match value {
            KeySlot::Signature => KeyType::Signing,
            KeySlot::Encryption => KeyType::Decryption,
            KeySlot::Authentication => KeyType::Authentication,
            KeySlot::Attestation => KeyType::Attestation,
        }
    }
}

#[pyfunction]
pub fn get_keyslot_touch_policy(py: Python, slot: Py<KeySlot>) -> Result<Py<TouchMode>> {
    let actual_slot: KeySlot = slot.extract(py)?;
    let policy = scard::touch_policy(actual_slot.into())?;

    Ok(Py::new(py, TouchMode::try_from(policy)?)?)
}

#[pyfunction]
pub fn set_keyslot_touch_policy(
    py: Python,
    adminpin: Vec<u8>,
    slot: Py<KeySlot>,
    mode: Py<TouchMode>,
) -> Result<bool> {
    let slot: KeySlot = slot.extract(py)?;
    let mode: TouchMode = mode.extract(py)?;

    scard::set_touch_policy(slot.into(), mode.into(), adminpin)
}

#[pyfunction]
pub fn enable_otp_usb() -> Result<bool> {
    match scard::change_otp(true) {
        Ok(value) => Ok(value),
        Err(value) => Err(CardError::new_err(format!("Error {}", value)).into()),
    }
}

#[pyfunction]
pub fn disable_otp_usb() -> Result<bool> {
    match scard::change_otp(false) {
        Ok(value) => Ok(value),
        Err(value) => Err(CardError::new_err(format!("Error {}", value)).into()),
    }
}

/// A Python module implemented in Rust.
#[pymodule]
fn johnnycanencrypt(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_wrapped(wrap_pyfunction!(is_smartcard_connected))?;
    m.add_wrapped(wrap_pyfunction!(reset_yubikey))?;
    m.add_wrapped(wrap_pyfunction!(change_admin_pin))?;
    m.add_wrapped(wrap_pyfunction!(change_user_pin))?;
    m.add_wrapped(wrap_pyfunction!(sign_bytes_detached_on_card))?;
    m.add_wrapped(wrap_pyfunction!(sign_file_detached_on_card))?;
    m.add_wrapped(wrap_pyfunction!(sign_file_on_card))?;
    m.add_wrapped(wrap_pyfunction!(set_name))?;
    m.add_wrapped(wrap_pyfunction!(set_url))?;
    m.add_wrapped(wrap_pyfunction!(get_card_details))?;
    m.add_wrapped(wrap_pyfunction!(decrypt_bytes_on_card))?;
    m.add_wrapped(wrap_pyfunction!(decrypt_file_on_card))?;
    m.add_wrapped(wrap_pyfunction!(decrypt_filehandler_on_card))?;
    m.add_wrapped(wrap_pyfunction!(create_key))?;
    m.add_wrapped(wrap_pyfunction!(upload_to_smartcard))?;
    m.add_wrapped(wrap_pyfunction!(upload_primary_to_smartcard))?;
    m.add_wrapped(wrap_pyfunction!(get_pub_key))?;
    m.add_wrapped(wrap_pyfunction!(bytes_encrypted_for))?;
    m.add_wrapped(wrap_pyfunction!(file_encrypted_for))?;
    m.add_wrapped(wrap_pyfunction!(merge_keys))?;
    m.add_wrapped(wrap_pyfunction!(encrypt_filehandler_to_file))?;
    m.add_wrapped(wrap_pyfunction!(parse_cert_file))?;
    m.add_wrapped(wrap_pyfunction!(parse_cert_bytes))?;
    m.add_wrapped(wrap_pyfunction!(encrypt_bytes_to_file))?;
    m.add_wrapped(wrap_pyfunction!(encrypt_bytes_to_bytes))?;
    m.add_wrapped(wrap_pyfunction!(encrypt_file_internal))?;
    m.add_wrapped(wrap_pyfunction!(update_password))?;
    m.add_wrapped(wrap_pyfunction!(add_uid_in_cert))?;
    m.add_wrapped(wrap_pyfunction!(revoke_uid_in_cert))?;
    m.add_wrapped(wrap_pyfunction!(update_subkeys_expiry_in_cert))?;
    m.add_wrapped(wrap_pyfunction!(certify_key))?;
    m.add_wrapped(wrap_pyfunction!(get_ssh_pubkey))?;
    m.add_wrapped(wrap_pyfunction!(get_signing_pubkey))?;
    m.add_wrapped(wrap_pyfunction!(get_card_version))?;
    m.add_wrapped(wrap_pyfunction!(get_keyslot_touch_policy))?;
    m.add_wrapped(wrap_pyfunction!(set_keyslot_touch_policy))?;
    m.add_wrapped(wrap_pyfunction!(enable_otp_usb))?;
    m.add_wrapped(wrap_pyfunction!(disable_otp_usb))?;
    m.add_wrapped(wrap_pyfunction!(get_key_cipher_details))?;
    m.add("CryptoError", _py.get_type::<CryptoError>())?;
    m.add("SameKeyError", _py.get_type::<SameKeyError>())?;
    m.add_class::<Johnny>()?;
    m.add_class::<TouchMode>()?;
    m.add_class::<KeySlot>()?;
    Ok(())
}
