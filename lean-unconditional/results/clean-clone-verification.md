# Clean-clone verification

**Result: pass.** A staged throwaway Git repository was cloned with `--no-hardlinks`, and the delivered `scripts/verify.sh` was run in the fresh clone. The user's root repository was not committed to or pushed.

```text
CLEAN_CLONE_HEAD 0f04aad582308a77bf57c35ed800b342ac85710f
CLEAN_CLONE_BUILD_ARTIFACTS_BEFORE absent
CLEAN_CLONE_VERIFY_EXIT 0
AUDIT_DECL_COUNT 1803
AUDIT_BAD_COUNT 0
Build completed successfully (9114 jobs).
```

The clone bootstrapped the official Lean 4.35.0 release, materialized the exact revisions in `lake-manifest.json`, fetched the Mathlib cache, and built the project without pre-existing project build artifacts. The full output is `clean-clone-build.log`.

The proof-source hashes in the clone match the working tree, including:

```text
15f09f8002cdc7c9dbf53e645c83649ff5c5084129b4c4f4e4f7d45805b76cc6  OrderedRemoval/Unconditional.lean
b2625ddfcff3d792375faa0ed3f05f3ee15c7e83b4ec7755825c40438082c5d4  OrderedRemoval/Statements.lean
```

The complete delivered source set has 66 Lean files: 61 OAI modules, three `OrderedRemoval` modules, and two root aggregation modules. Report and inventory files added after this proof-source run do not affect `scripts/verify.sh`, Lake configuration, imports, or compiled declarations.
