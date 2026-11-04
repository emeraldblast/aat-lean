"""Send a Lean file to the DeepSeek API for adversarial review.

Usage:
    export DEEPSEEK_API_KEY=sk-...
    python3 review/deepseek_review.py [file.lean] [prompt.txt]

Env:
    DEEPSEEK_MODEL  model name (default: deepseek-reasoner)
"""
import json
import os
import pathlib
import sys
import urllib.error
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent
API_URL = "https://api.deepseek.com/chat/completions"


def main() -> None:
    key = os.environ.get("DEEPSEEK_API_KEY")
    if not key:
        sys.exit("DEEPSEEK_API_KEY is not set")

    lean_path = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "AatLean/Chain.lean"
    prompt_path = pathlib.Path(sys.argv[2]) if len(sys.argv) > 2 else ROOT / "review/prompt.txt"
    model = os.environ.get("DEEPSEEK_MODEL", "deepseek-reasoner")

    content = prompt_path.read_text() + "\n\nCode:\n```lean\n" + lean_path.read_text() + "\n```\n"
    body = json.dumps({
        "model": model,
        "messages": [{"role": "user", "content": content}],
    }).encode()

    req = urllib.request.Request(API_URL, data=body, headers={
        "Content-Type": "application/json",
        "Authorization": f"Bearer {key}",
    })
    try:
        with urllib.request.urlopen(req, timeout=600) as resp:
            data = json.load(resp)
    except urllib.error.HTTPError as e:
        sys.exit(f"HTTP {e.code}: {e.read().decode(errors='replace')}")

    answer = data["choices"][0]["message"]["content"]
    out_dir = ROOT / "review/out"
    out_dir.mkdir(exist_ok=True)
    out = out_dir / f"{model}-{data.get('id', 'reply')}.md"
    out.write_text(answer)
    print(answer)
    print(f"\n--- saved to {out}", file=sys.stderr)


if __name__ == "__main__":
    main()
