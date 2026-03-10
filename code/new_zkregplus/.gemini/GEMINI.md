## Context Management & Token Optimization
- **Model Choice:** Always use `gemini-3-flash-preview` as the primary model. You MUST ask for user permission before switching to or using any `gemini-pro` models.
- **Token Efficiency:** Keep tool outputs minimal. When editing code, provide only targeted, surgical code edits. Avoid rewriting entire files or printing out unmodified code.
- **Usage Warnings:** Proactively warn the user if a request requires processing massive amounts of data or generating excessive tokens (e.g., reading large directories, massive logs). Monitor the session and alert the user approximately every time an additional 1 million input or output tokens are consumed.
- **Limit Errors:** Ensure the full details of any model limit or quota errors are clearly communicated to the user immediately.

## Rust & Cryptography Project Guidelines
- **Libraries:** This project utilizes `arkworks` and `sonobe`. Prioritize these libraries for cryptographic primitives, finite fields, algebraic curves, and zero-knowledge proofs over alternatives.
- **Tooling:** Always use standard `cargo` tooling (`cargo check`, `cargo build`, `cargo clippy`) for validation. When fixing compiler or clippy errors, provide minimal and precise fixes. Do not run Cargo test
- **Style:** Adhere strictly to standard Rust idioms, safety practices, and formatting. Do not introduce unsafe blocks unless explicitly required and justified.

- **Code Insertion:** Whenever inserting or modifying code, ensure the line width does not exceed 80 characters. Maintain consistency with the project's existing coding style and formatting.

## Task Management
- **Task Identification:** When asked to "complete Task" in a file, focus solely on the specified tasks, which are typically accompanied by an ID (e.g., Task 1, Task 3.2.5).
- **Task Completion & Cancellation:** If the "Esc" option is chosen from a menu, regard it as task completion.
- **Cost Estimation:** Upon completing a task (or when "Esc" is chosen), output the number of tokens used and provide an estimated cost for executing the tasks.
