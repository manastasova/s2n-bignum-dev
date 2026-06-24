Read-only local copies of the AES-XTS encrypt proof, extracted from git branch
nebeid/aes-xts-enc (not on the working tree).  Kept here purely as a structural
reference for the AES-GCM single-binary proofs in ../aes256_gcm.ml — to mirror
XTS conventions (named parameterized sub-tactics, ENSURES_SEQUENCE_TAC shared
tails, band-lemma layout).  NOT loaded by any build; do not `needs` these.

  aes-xts-armv8.ml        - the main XTS encrypt proof (band lemmas + tail)
  aes_xts_encrypt_spec.ml - the XTS functional spec

Source: git show nebeid/aes-xts-enc:arm/proofs/aes-xts-armv8.ml
