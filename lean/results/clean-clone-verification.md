# Clean-clone verification

- Snapshot commit: `1f5352b2f249361dc5ecd331289b92571dd2b0f4`
- Method: temporary local Git source repository, cloned with `--no-hardlinks`. The primary project repository was not committed to or otherwise changed.
- Initial clone state: 9 tracked source files; no `.lake` directory and no `.scratch` directory.
- Command run inside clone: `./scripts/verify.sh`
- Lean: 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, downloaded by the script)
- Mathlib: v4.35.0, `56a005855ea17e0b0958f73ec801ae140b0a1679` (fetched at the pinned revision)
- `OrderedRemoval/Statements.lean` SHA-256, both source and clone: `b2625ddfcff3d792375faa0ed3f05f3ee15c7e83b4ec7755825c40438082c5d4`

Final output:

```text
AUDIT_DECL_COUNT 507
AUDIT_BAD_COUNT 0
Build completed successfully (2074 jobs).
```

The script exited `0`. The build emitted non-fatal deprecation and linter warnings; it emitted no errors and no `sorry` warnings.
