"""Ed25519 signature check through OpenSSL (Homebrew, OpenSSL >= 3)."""
import base64
import pathlib
import subprocess
import tempfile

import os
import shutil

# OpenSSL >= 3 with Ed25519; macOS system LibreSSL lacks it, so prefer Homebrew.
OPENSSL = os.environ.get("OPENSSL") or next(
    (p for p in ("/opt/homebrew/bin/openssl", "/usr/local/opt/openssl/bin/openssl")
     if os.path.exists(p)), shutil.which("openssl") or "openssl")
SPKI_PREFIX = bytes.fromhex("302a300506032b6570032100")  # SubjectPublicKeyInfo for Ed25519


def b64u_decode(s):
    return base64.urlsafe_b64decode(s + "=" * (-len(s) % 4))


def verify(jwk_x_b64u, message: bytes, signature: bytes) -> bool:
    try:
        x = b64u_decode(jwk_x_b64u)
    except Exception:
        return False
    if len(x) != 32 or len(signature) != 64:
        return False
    with tempfile.TemporaryDirectory() as d:
        d = pathlib.Path(d)
        (d / "k.der").write_bytes(SPKI_PREFIX + x)
        (d / "m").write_bytes(message)
        (d / "s").write_bytes(signature)
        r = subprocess.run([OPENSSL, "pkeyutl", "-verify", "-pubin", "-inkey", str(d / "k.der"),
                            "-keyform", "DER", "-rawin", "-in", str(d / "m"), "-sigfile", str(d / "s")],
                           capture_output=True)
        return r.returncode == 0
