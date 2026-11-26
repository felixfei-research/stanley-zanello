# Finite checks

Run from this directory with Python 3 (standard library only).

```sh
python3 verify_sz.py --max-k 16 --max-width 160 --output-dir reproduced
diff deterministic_sha256.json reproduced/deterministic_sha256.json
```

The digest list covers the verifier, the supplied comparison fixture and five deterministic output files. The separate run metadata contains environment-dependent paths and timing. The full delivery includes the observed outputs in `verification/results`. The arXiv ancillary directory includes the inputs needed to regenerate them. The Lean proof neither imports nor calls this program.
