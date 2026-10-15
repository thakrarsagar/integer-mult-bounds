# Vendored file notice

`check_p104_relay_construction.py` is the published P104 relay checker by Philippe Van Velzen. It was prepared with
Claude Code assistance, as its README states.

It is copied **byte-for-byte, unchanged** from:

- Repository: `philippeVV/integer-mult-bounds`. This is a fork of `CrocSwap/integer-mult-bounds`, and the license
  reported by GitHub is Apache-2.0.
- Commit: `fac9e821d31bc199b49e8ed463074a50d1264311`.
- Path: `research/p104-correction-screen/relay-construction/check_p104_relay_construction.py`.
- Git blob: `d8a249db16ead8bfb8b47336ab5ce3a8133e1783`.
- SHA-256: `b808e70129fc2c01fbead974c770e0a39245f3a3968c53bcd1f49fb1972e865d`.

`../verify.py` refuses to run unless the bytes match this SHA-256. It invokes the checker as
`python3 -I -B check_p104_relay_construction.py REPO_ROOT WORD.json`, in a separate process. Attribution remains with
the original author.
