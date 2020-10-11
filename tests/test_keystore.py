import datetime
import os
import shutil
import tempfile

import pytest

import johnnycanencrypt as jce

from .utils import clean_outputfiles, verify_files

DATA = "Kushal loves 🦀"


def setup_module(module):
    module.tmpdirname = tempfile.TemporaryDirectory()


def teardown_module(module):
    del module.tmpdirname


def test_correct_keystore_path():
    ks = jce.KeyStore("tests/files/store")


def test_nonexisting_keystore_path():
    with pytest.raises(OSError):
        ks = jce.KeyStore("tests/files2/")


def test_no_such_key():
    with pytest.raises(jce.KeyNotFoundError):
        ks = jce.KeyStore("tests/files/store")
        key = ks.get_key("BB2D3F20233286371C3123D5209940B9669ED677")


def test_keystore_lifecycle():
    ks = jce.KeyStore(tmpdirname.name)
    newkey = ks.create_newkey("redhat", "test key1 <email@example.com>", "RSA4k")
    # the default key must be of secret
    assert newkey.keytype == 1

    ks.import_cert("tests/files/store/public.asc")
    ks.import_cert("tests/files/store/pgp_keys.asc")
    ks.import_cert("tests/files/store/hellopublic.asc")
    ks.import_cert("tests/files/store/secret.asc")
    # Now check the numbers of keys in the store
    assert (2, 2) == ks.details()

    ks.delete_key("BB2D3F20233286371C3123D5209940B9669ED621")
    assert (2, 1) == ks.details()

    # Now verify email cache
    key_via_fingerprint = ks.get_key("A85FF376759C994A8A1168D8D8219C8C43F6C5E1")
    keys_via_emails = ks.get_keys(qvalue="kushaldas@gmail.com", qtype="email")
    assert len(keys_via_emails) == 1
    assert key_via_fingerprint == keys_via_emails[0]

    # Now verify name cache
    key_via_fingerprint = ks.get_key("6AC6957E2589CB8B5221F6508ADA07F0A0F7BA99")
    keys_via_names = ks.get_keys(qvalue="test key", qtype="value")
    assert len(keys_via_names) == 1
    assert key_via_fingerprint == keys_via_names[0]


def test_keystore_contains_key():
    "verifies __contains__ method for keystore"
    ks = jce.KeyStore(tmpdirname.name)
    keypath = "tests/files/store/secret.asc"
    k = ks.import_cert(keypath)
    _, fingerprint, keytype, exp, ctime = jce.parse_cert_file(keypath)

    # First only the fingerprint
    assert fingerprint in ks
    # Next the Key object
    assert k in ks
    # This should be false
    with pytest.raises(jce.KeyNotFoundError):
        "1111111" in ks


def test_keystore_details():
    ks = jce.KeyStore("./tests/files/store")
    assert (1, 2) == ks.details()


def test_keystore_key_uids():
    ks = jce.KeyStore("./tests/files/store")
    key = ks.get_key("A85FF376759C994A8A1168D8D8219C8C43F6C5E1")
    assert "kushal@fedoraproject.org" == key.uids[0]["email"]
    assert "mail@kushaldas.in" == key.uids[-1]["email"]


def test_key_deletion():
    tempdir = tempfile.TemporaryDirectory()
    ks = jce.KeyStore(tempdir.name)
    ks.import_cert("tests/files/store/public.asc")
    ks.import_cert("tests/files/store/pgp_keys.asc")
    ks.import_cert("tests/files/store/hellopublic.asc")
    ks.import_cert("tests/files/store/hellosecret.asc")
    ks.import_cert("tests/files/store/secret.asc")
    assert (1, 2) == ks.details()

    ks.delete_key("BB2D3F20233286371C3123D5209940B9669ED621")
    assert (1, 1) == ks.details()

    # Now delete both public and secret
    ks.delete_key("6AC6957E2589CB8B5221F6508ADA07F0A0F7BA99")
    assert (1, 0) == ks.details()


def test_key_equality():
    ks = jce.KeyStore("tests/files/store")
    key = ks.get_key("6AC6957E2589CB8B5221F6508ADA07F0A0F7BA99")
    assert key.fingerprint == "6AC6957E2589CB8B5221F6508ADA07F0A0F7BA99"


def test_ks_encrypt_decrypt_bytes():
    "Encrypts and decrypt some bytes"
    ks = jce.KeyStore("tests/files/store")
    public_key = ks.get_key("6AC6957E2589CB8B5221F6508ADA07F0A0F7BA99")
    encrypted = ks.encrypt(public_key, DATA)
    assert encrypted.startswith(b"-----BEGIN PGP MESSAGE-----\n")
    secret_key = ks.get_key("6AC6957E2589CB8B5221F6508ADA07F0A0F7BA99")
    decrypted_text = ks.decrypt(secret_key, encrypted, password="redhat").decode(
        "utf-8"
    )
    assert DATA == decrypted_text


def test_ks_encrypt_decrypt_bytes_multiple_recipients():
    "Encrypts and decrypt some bytes"
    ks = jce.KeyStore("tests/files/store")
    key1 = ks.get_key("6AC6957E2589CB8B5221F6508ADA07F0A0F7BA99")
    key2 = ks.get_key("BB2D3F20233286371C3123D5209940B9669ED621")
    encrypted = ks.encrypt([key1, key2], DATA)
    assert encrypted.startswith(b"-----BEGIN PGP MESSAGE-----\n")
    secret_key1 = ks.get_key("6AC6957E2589CB8B5221F6508ADA07F0A0F7BA99")
    decrypted_text = ks.decrypt(secret_key1, encrypted, password="redhat").decode(
        "utf-8"
    )
    assert DATA == decrypted_text
    secret_key2 = ks.get_key("BB2D3F20233286371C3123D5209940B9669ED621")
    decrypted_text = ks.decrypt(secret_key2, encrypted, password="redhat").decode(
        "utf-8"
    )
    assert DATA == decrypted_text


def test_ks_encrypt_decrypt_bytes_to_file():
    "Encrypts and decrypt some bytes"
    outputfile = os.path.join(tmpdirname.name, "encrypted.asc")
    ks = jce.KeyStore("tests/files/store")
    secret_key = ks.get_key("6AC6957E2589CB8B5221F6508ADA07F0A0F7BA99")
    assert ks.encrypt(secret_key, DATA, outputfile=outputfile)
    with open(outputfile, "rb") as fobj:
        encrypted = fobj.read()
    secret_key = ks.get_key("6AC6957E2589CB8B5221F6508ADA07F0A0F7BA99")
    decrypted_text = ks.decrypt(secret_key, encrypted, password="redhat").decode(
        "utf-8"
    )
    assert DATA == decrypted_text


def test_ks_encrypt_decrypt_bytes_to_file_multiple_recipients():
    "Encrypts and decrypt some bytes"
    outputfile = os.path.join(tmpdirname.name, "encrypted.asc")
    ks = jce.KeyStore("tests/files/store")
    key1 = ks.get_key("6AC6957E2589CB8B5221F6508ADA07F0A0F7BA99")
    key2 = ks.get_key("BB2D3F20233286371C3123D5209940B9669ED621")
    assert ks.encrypt([key1, key2], DATA, outputfile=outputfile)
    with open(outputfile, "rb") as fobj:
        encrypted = fobj.read()
    secret_key = ks.get_key("6AC6957E2589CB8B5221F6508ADA07F0A0F7BA99")
    decrypted_text = ks.decrypt(secret_key, encrypted, password="redhat").decode(
        "utf-8"
    )
    assert DATA == decrypted_text


def test_ks_encrypt_decrypt_file(encrypt_decrypt_file):
    "Encrypts and decrypt some bytes"
    inputfile = "tests/files/text.txt"
    output = "/tmp/text-encrypted.pgp"
    decrypted_output = "/tmp/text.txt"

    ks = jce.KeyStore("tests/files/store")
    public_key = ks.get_key("6AC6957E2589CB8B5221F6508ADA07F0A0F7BA99")
    assert ks.encrypt_file(public_key, inputfile, output)
    secret_key = ks.get_key("6AC6957E2589CB8B5221F6508ADA07F0A0F7BA99")
    ks.decrypt_file(secret_key, output, decrypted_output, password="redhat")
    verify_files(inputfile, decrypted_output)


def test_ks_encrypt_decrypt_file_multiple_recipients(encrypt_decrypt_file):
    "Encrypts and decrypt some bytes"
    inputfile = "tests/files/text.txt"
    output = "/tmp/text-encrypted.pgp"
    decrypted_output = "/tmp/text.txt"

    ks = jce.KeyStore("tests/files/store")
    key1 = ks.get_key("6AC6957E2589CB8B5221F6508ADA07F0A0F7BA99")
    key2 = ks.get_key("BB2D3F20233286371C3123D5209940B9669ED621")
    encrypted = ks.encrypt_file([key1, key2], inputfile, output)
    secret_key1 = ks.get_key("6AC6957E2589CB8B5221F6508ADA07F0A0F7BA99")
    ks.decrypt_file(secret_key1, output, decrypted_output, password="redhat")
    verify_files(inputfile, decrypted_output)
    secret_key2 = ks.get_key("BB2D3F20233286371C3123D5209940B9669ED621")
    ks.decrypt_file(secret_key2, output, decrypted_output, password="redhat")
    verify_files(inputfile, decrypted_output)


def test_ks_sign_data():
    ks = jce.KeyStore("tests/files/store")
    key = "6AC6957E2589CB8B5221F6508ADA07F0A0F7BA99"
    signed = ks.sign(key, "hello", "redhat")
    assert signed.startswith("-----BEGIN PGP SIGNATURE-----\n")
    assert ks.verify(key, "hello", signed)


def test_ks_sign_data_fails():
    ks = jce.KeyStore("tests/files/store")
    key = "6AC6957E2589CB8B5221F6508ADA07F0A0F7BA99"
    signed = ks.sign(key, "hello", "redhat")
    assert signed.startswith("-----BEGIN PGP SIGNATURE-----\n")
    assert not ks.verify(key, "hello2", signed)


def test_ks_sign_verify_file():
    inputfile = "tests/files/text.txt"
    tempdir = tempfile.TemporaryDirectory()
    shutil.copy(inputfile, tempdir.name)
    ks = jce.KeyStore("tests/files/store")
    key = "6AC6957E2589CB8B5221F6508ADA07F0A0F7BA99"
    file_to_be_signed = os.path.join(tempdir.name, "text.txt")
    signed = ks.sign_file(key, file_to_be_signed, "redhat", write=True)
    assert signed.startswith("-----BEGIN PGP SIGNATURE-----\n")
    assert ks.verify_file(key, file_to_be_signed, file_to_be_signed + ".asc")


def test_ks_creation_expiration_time():
    """
    Tests via Kushal's key and a new key
    """
    # These two are known values from kushal
    etime = datetime.datetime(2020, 10, 16, 20, 53, 47)
    ctime = datetime.datetime(2017, 10, 17, 20, 53, 47)
    tmpdir = tempfile.TemporaryDirectory()
    # First let us check from the file
    keypath = "tests/files/store/pgp_keys.asc"
    ks = jce.KeyStore(tmpdir.name)
    k = ks.import_cert(keypath)
    assert etime == k.expirationtime
    assert ctime == k.creationtime

    # now with a new key and creation time
    ctime = datetime.datetime(2010, 10, 10, 20, 53, 47)
    newk = ks.create_newkey("redhat", "Another test key", creation=ctime)
    assert ctime == newk.creationtime
    assert not newk.expirationtime

    # Now both creation and expirationtime
    ctime = datetime.datetime(2008, 10, 10, 20, 53, 47)
    etime = datetime.datetime(2025, 12, 15, 20, 53, 47)
    newk = ks.create_newkey(
        "redhat", "Another test key", creation=ctime, expiration=etime
    )
    assert ctime == newk.creationtime
    assert etime == newk.expirationtime
