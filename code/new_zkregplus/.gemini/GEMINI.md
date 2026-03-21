## Custom Command Workflow
- **PLAN:** When `/plan` is called, perform research and strategy. Do NOT modify workspace files. Provide a clear plan and wait for feedback.
- **WRITE_PLAN:** When `/write_plan` is called, stage proposed changes in temporary files and initiate a `vimdiff` for each file. Wait for approval.
- **EXECUTE:** When `/execute` is called, apply the approved changes to the workspace and validate with `cargo check`.

## Context Management & Token Optimization
- **Model Choice:** Always use `gemini-3-flash-preview` as the primary model. You MUST ask for user permission before switching to or using any `gemini-pro` models.
- **Token Efficiency:** Keep tool outputs minimal. When editing code, provide only targeted, surgical code edits. Avoid rewriting entire files or printing out unmodified code.
- **Usage Warnings:** Proactively warn the user if a request requires processing massive amounts of data or generating excessive tokens (e.g., reading large directories, massive logs). Monitor the session and alert the user approximately every time an additional 1 million input or output tokens are consumed.
- **Limit Errors:** Ensure the full details of any model limit or quota errors are clearly communicated to the user immediately.

## Rust & Cryptography Project Guidelines
- **Libraries:** This project utilizes `arkworks`. Prioritize these libraries for cryptographic primitives, finite fields, algebraic curves, and zero-knowledge proofs over alternatives.
- **Tooling:** Always use standard `cargo` tooling (`cargo check`, `cargo build`, `cargo clippy`) for validation. When fixing compiler or clippy errors, provide minimal and precise fixes. Do not run Cargo test
- **Style:** Adhere strictly to standard Rust idioms, safety practices, and formatting. Do not introduce unsafe blocks unless explicitly required and justified.

- **Code Insertion:** Whenever inserting or modifying code, ensure the line width does not exceed 80 characters. Maintain consistency with the project's existing coding style and formatting.

