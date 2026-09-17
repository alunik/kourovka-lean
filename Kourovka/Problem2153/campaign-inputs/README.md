# Certificate producer inputs

These are the exact finite data used by the certificate producers in the parent
result tree, together with their small Python arithmetic helpers. The retained
JSON bytes come from the recorded campaign; the producer paths were made
relative for this release. The helpers require Python 3 and NumPy.

The trusted mathematical artifacts are the committed Lean sources and their
kernel proofs. The Python programs are untrusted research producers; they are
not called by the Lean build and supply no assumed axiom. Some proof scripts
were subsequently reorganized by hand. Run generators only in a fresh copy and
compare outputs before considering any replacement. The accepted source
manifest identifies the exact proved files, independently of generator output.

The arithmetic model follows Wilson's published matrices, with Wilson's credit
to Coolsaet retained in the result README. All six input/helper files are
included so the producer scripts do not depend on a private campaign directory.
