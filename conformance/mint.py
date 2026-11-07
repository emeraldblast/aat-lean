"""Mint AAT-02 tokens and PoP JWTs: compact JWS signed with Ed25519 (OpenSSL)."""
import base64
import hashlib
import json
import pathlib
import subprocess
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent / "vectors"))
import ed25519  # noqa: E402  (OPENSSL lookup, b64u_decode)

PKCS8_PREFIX = bytes.fromhex("302e020100300506032b657004220420")  # Ed25519 private key, RFC 8410


def b64u(b: bytes) -> str:
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode()


def compact_json(obj) -> str:
    return json.dumps(obj, separators=(",", ":"), ensure_ascii=False)


def sign(seed_hex: str, message: bytes) -> bytes:
    with tempfile.TemporaryDirectory() as d:
        d = pathlib.Path(d)
        (d / "k.der").write_bytes(PKCS8_PREFIX + bytes.fromhex(seed_hex))
        (d / "m").write_bytes(message)
        subprocess.run([ed25519.OPENSSL, "pkeyutl", "-sign", "-inkey", str(d / "k.der"), "-keyform", "DER",
                        "-rawin", "-in", str(d / "m"), "-out", str(d / "s")], check=True, capture_output=True)
        return (d / "s").read_bytes()


def jws(header: dict, payload: dict, seed_hex: str, signer: str, payload_json: str = None) -> dict:
    """A token in the same shape as the upstream suite's `chain` entries."""
    pj = payload_json if payload_json is not None else compact_json(payload)
    hb, pb = b64u(compact_json(header).encode()), b64u(pj.encode())
    si = f"{hb}.{pb}"
    sig = b64u(sign(seed_hex, si.encode()))
    return {"header": header, "payload": payload, "payload_json": pj, "header_b64": hb, "payload_b64": pb,
            "signing_input": si, "signing_input_sha256_b64u": b64u(hashlib.sha256(si.encode()).digest()),
            "signature_b64": sig, "compact": f"{si}.{sig}", "signer": signer}


def thumbprint_uri(jwk: dict) -> str:
    canon = json.dumps({"crv": jwk["crv"], "kty": jwk["kty"], "x": jwk["x"]}, separators=(",", ":"), sort_keys=True)
    return "urn:ietf:params:oauth:jwk-thumbprint:sha-256:" + b64u(hashlib.sha256(canon.encode()).digest())


if __name__ == "__main__":
    # self-test: re-sign J.1's root with the control_plane seed; Ed25519 is deterministic
    suite = json.load(open(sys.argv[1]))
    v = suite["vectors"][0]
    t = v["chain"][0]
    seed = suite["keys"][t["signer"]]["seed_hex"]
    ours = b64u(sign(seed, t["signing_input"].encode()))
    print("signer:", t["signer"])
    print("signature matches the author's byte for byte:", ours == t["signature_b64"])
