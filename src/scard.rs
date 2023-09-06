// SPDX-FileCopyrightText: © 2020 Kushal Das <mail@kushaldas.in>
// SPDX-License-Identifier: LGPL-3.0-or-later

use crate::{CardError, JceError};
use card_backend::CardBackend;
use card_backend_pcsc::PcscBackend;
use openpgp::cert::amalgamation::{key::ValidErasedKeyAmalgamation, ValidateAmalgamation};
use openpgp::packet::key::SecretParts;
use openpgp::packet::prelude::SignatureBuilder;
use openpgp::parse::stream::DecryptorBuilder;
use openpgp::parse::Parse;
use openpgp::policy::StandardPolicy;
use openpgp::serialize::stream::{Armorer, LiteralWriter, Message, Signer};
use openpgp::types::SignatureType;
use openpgp_card_sequoia::types::{KeyType, TouchPolicy};
use openpgp_card_sequoia::{sq_util, state::Open, Card};
use yubikey_management::{Application, YkManagement};

/// Result Generic Type for the module.
pub(crate) type Result<T> = std::result::Result<T, JceError>;

pub(crate) fn is_smartcard_connected() -> Result<bool> {
    Ok(first_pcsc_card().is_ok())
}

/// Get the first card that allows SELECT on the OpenPGP card application
pub(crate) fn first_pcsc_card() -> Result<Card<Open>> {
    if let Ok(cards) = PcscBackend::card_backends(None) {
        for backend in cards.filter_map(|c| c.ok()) {
            let res = Card::<Open>::new(backend as Box<dyn CardBackend + Send + Sync>);
            if let Ok(card) = res {
                // TODO? filter for YubiKeys, by manufacturer field

                return Ok(card);
            }
        }
    }

    Err(JceError::new("No card found".to_string()))
}

pub(crate) struct CardDetails {
    pub serial: u32,
    pub cardholder_name: String,
    pub url: String,
    pub sig_fp: Vec<u8>,
    pub enc_fp: Vec<u8>,
    pub aut_fp: Vec<u8>,
    pub pw1: u8,
    pub rc: u8,
    pub pw3: u8,
    pub signature_count: u32,
}

pub(crate) fn get_card_details() -> Result<CardDetails> {
    let mut card = first_pcsc_card()?;
    let mut tx = card.transaction()?;

    // Now let us get the serial number
    let ai = tx
        .application_identifier()
        .map_err(|err| CardError::new_err(format!("Error in getting AID: {}", err)))?;
    let serial = ai.serial();

    // Now the name of the card holder
    let cardholder_name = tx
        .cardholder_name()
        .map_err(|_| CardError::new_err("Card reading error for name."))?;

    // Let us get the URL of the public key
    let url = tx.url()?;

    // Get fingerprints
    fn fp_to_vec(fp: Option<&openpgp_card_sequoia::types::Fingerprint>) -> Vec<u8> {
        fp.map(|f| f.as_bytes().to_vec()).unwrap_or(vec![])
    }

    let fps = tx.fingerprints()?;
    let sig_fp = fp_to_vec(fps.signature());
    let enc_fp = fp_to_vec(fps.decryption());
    let aut_fp = fp_to_vec(fps.authentication());

    // Pin retries left
    let pwstatus = tx
        .pw_status_bytes()
        .map_err(|_| CardError::new_err("Error in getting pin retries left."))?;
    let pw1 = pwstatus.err_count_pw1();
    let rc = pwstatus.err_count_rc();
    let pw3 = pwstatus.err_count_pw3();

    // Get the Security support template
    let signature_count = tx.digital_signature_count().map_err(|err| {
        CardError::new_err(format!("Error in getting security template: {}", err))
    })?;

    let cd = CardDetails {
        serial,
        cardholder_name,
        url,
        sig_fp,
        enc_fp,
        aut_fp,
        pw1,
        rc,
        pw3,
        signature_count,
    };

    Ok(cd)
}

pub(crate) fn reset_yk() -> Result<bool> {
    let mut card = first_pcsc_card()?;
    card.transaction()?.factory_reset()?;

    Ok(true)
}

pub(crate) fn change_user_pin(adminpin: Vec<u8>, newpin: Vec<u8>) -> Result<bool> {
    let mut card = first_pcsc_card()?;
    let mut tx = card.transaction()?;

    let mut admin = tx
        .to_admin_card(&adminpin)
        .map_err(|_| JceError::new("Failed to switch card to Admin mode".to_string()))?;

    admin.reset_user_pin(String::from_utf8_lossy(&newpin).as_ref())?;

    Ok(true)
}

pub(crate) fn change_admin_pin(adminpin: Vec<u8>, newadminpin: Vec<u8>) -> Result<bool> {
    let mut card = first_pcsc_card()?;
    card.transaction()?.change_admin_pin(
        String::from_utf8_lossy(&adminpin).as_ref(),
        String::from_utf8_lossy(&newadminpin).as_ref(),
    )?;

    Ok(true)
}

pub(crate) fn set_name(name: &str, pin: Vec<u8>) -> Result<bool> {
    let mut card = first_pcsc_card()?;
    let mut tx = card.transaction()?;

    let mut admin = tx
        .to_admin_card(&pin)
        .map_err(|_| JceError::new("Failed to switch card to Admin mode".to_string()))?;

    admin.set_cardholder_name(name)?;

    Ok(true)
}

pub(crate) fn set_url(url: Vec<u8>, pin: Vec<u8>) -> Result<bool> {
    let mut card = first_pcsc_card()?;
    let mut tx = card.transaction()?;

    let mut admin = tx
        .to_admin_card(&pin)
        .map_err(|_| JceError::new("Failed to switch card to Admin mode".to_string()))?;

    admin.set_url(String::from_utf8_lossy(&url).as_ref())?;

    Ok(true)
}

pub(crate) fn firmware_version_yubico() -> Result<Vec<u8>> {
    let mut card = first_pcsc_card()?;
    let version = card
        .transaction()?
        .firmware_version()
        .map_err(|_| JceError::new("Can not get YubiKey version".to_string()))?;

    Ok(version)
}

pub(crate) fn touch_policy(slot: KeyType) -> Result<TouchPolicy> {
    let mut card = first_pcsc_card()?;
    let tx = card.transaction()?;

    let uif = tx.user_interaction_flag(slot)?;

    uif.map(|uif| uif.touch_policy())
        .ok_or(JceError::new(format!(
            "Failed to get touch policy for slot {:?}",
            slot
        )))
}

pub(crate) fn set_touch_policy(
    slot: KeyType,
    policy: TouchPolicy,
    adminpin: Vec<u8>,
) -> Result<bool> {
    let mut card = first_pcsc_card()?;
    let mut tx = card.transaction()?;

    let mut admin = tx
        .to_admin_card(&adminpin)
        .map_err(|_| JceError::new("Failed to switch card to Admin mode".to_string()))?;

    admin.set_touch_policy(slot, policy)?;

    Ok(true)
}

pub(crate) fn decrypt_on_card<R, W>(read: R, write: &mut W, pin: Vec<u8>) -> Result<()>
where
    R: std::io::Read + Send + Sync,
    W: std::io::Write,
{
    let p = &StandardPolicy::new();

    let mut card = first_pcsc_card()?;
    let mut tx = card.transaction()?;

    let mut user = tx
        .to_user_card(&pin)
        .map_err(|_| JceError::new("Failed to switch card to User mode".to_string()))?;

    let d = user.decryptor(&|| println!("Touch confirmation needed for decryption"))?;

    let db = DecryptorBuilder::from_reader(read)?;
    let mut decryptor = db.with_policy(p, None, d)?;

    std::io::copy(&mut decryptor, write)?;

    Ok(())
}

pub(crate) fn sign_on_card_detached<R, W>(mut read: R, write: &mut W, pin: Vec<u8>) -> Result<()>
where
    R: std::io::Read + Send + Sync,
    W: std::io::Write + Send + Sync,
{
    let mut card = first_pcsc_card()?;
    let mut tx = card.transaction()?;

    let mut sign = tx
        .to_signing_card(&pin)
        .map_err(|_| JceError::new("Failed to switch card to Sign mode".to_string()))?;
    let s = sign.signer(&|| println!("Touch confirmation needed for signing"))?;

    let message = Armorer::new(Message::new(write)).build()?;
    let mut signer = Signer::new(message, s).detached().build()?;

    std::io::copy(&mut read, &mut signer)?;
    signer.finalize()?;

    Ok(())
}

pub(crate) fn sign_on_card<R, W>(
    mut read: R,
    mut write: W,
    pin: Vec<u8>,
    cleartext: bool,
) -> Result<()>
where
    R: std::io::Read + Send + Sync,
    W: std::io::Write + Send + Sync,
{
    let mut card = first_pcsc_card()?;
    let mut tx = card.transaction()?;

    let mut sign = tx
        .to_signing_card(&pin)
        .map_err(|_| JceError::new("Failed to switch card to Sign mode".to_string()))?;
    let s = sign.signer(&|| println!("Touch confirmation needed for signing"))?;

    // Stream an OpenPGP message.
    let mut message = Message::new(&mut write);
    if !cleartext {
        message = Armorer::new(message).build()?;
    };
    let builder = match cleartext {
        false => SignatureBuilder::new(SignatureType::Binary),
        true => SignatureBuilder::new(SignatureType::Text),
    };
    // Now, create a signer with the builder.
    let mut signer = Signer::with_template(message, s, builder);

    // Now if we need cleartext signature
    if cleartext {
        signer = signer.cleartext();
    }

    // Emit a literal data packet or direct writer for cleartext.
    let mut writer = match cleartext {
        false => LiteralWriter::new(signer.build()?).build()?,
        true => signer.build()?,
    };

    // Copy all the data.
    std::io::copy(&mut read, &mut writer).expect("Failed to sign data");

    // Finally, teardown the stack to ensure all the data is written.
    writer.finalize()?;

    Ok(())
}

/// keytype
/// 1 -- encryption key
/// 2 -- singing key
/// 3 -- authentication key
pub(crate) fn parse_and_move_a_key(
    cert: openpgp::Cert,
    keytype: i8,
    pin: Vec<u8>,
    password: String,
    primary: bool,
) -> Result<bool> {
    let policy = StandardPolicy::new();

    let key_type = match keytype {
        1 => KeyType::Decryption,
        2 => KeyType::Signing,
        3 => KeyType::Authentication,
        _ => unimplemented!(),
    };

    // The component key we want to upload
    let key: ValidErasedKeyAmalgamation<SecretParts> = if primary {
        // The primary
        let vpka = cert
            .primary_key()
            .with_policy(&policy, None)?
            .parts_into_secret()?;

        vpka.into()
    } else {
        // Subkey for `key_type` (with secret key material)
        sq_util::subkey_by_type(&cert, &policy, key_type)?.ok_or(JceError::new(format!(
            "Could not find a matching subkey for {:?}.",
            key_type
        )))?
    };

    let mut card = first_pcsc_card()?;
    let mut tx = card.transaction()?;

    let mut admin = tx
        .to_admin_card(&pin)
        .map_err(|_| JceError::new("Failed to switch card to Admin mode".to_string()))?;

    admin.upload_key(key, key_type, Some(password))?;

    Ok(true)
}

pub(crate) fn change_otp(value: bool) -> Result<bool> {
    let card = first_pcsc_card()?.into_backend();

    let mut ykm = YkManagement::select(card).map_err(openpgp_card_sequoia::types::Error::from)?;
    ykm.applications_change_usb(&[Application::Otp], value)
        .map_err(openpgp_card_sequoia::types::Error::from)?;

    Ok(true)
}
