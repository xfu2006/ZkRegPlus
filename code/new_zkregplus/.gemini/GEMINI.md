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

## Task Management & Cost Accounting
- **Task Identification:** When asked to "complete Task" in a file, focus solely on the specified tasks, which are typically accompanied by an ID (e.g., Task 1, Task 3.2.5).
- **Custom Commands:**
    - `/mytask <ID>: <description>`: Starts a specific task. You MUST include the internal slash command `/stats model` as plain text in your response immediately to record the current cumulative token counts as a baseline.
    - `/done <ID>`: Marks the completion of a task. You MUST include the internal slash command `/stats model` again as plain text in your response to calculate the final difference.
- **Critical Requirement for `/stats model`**: This is an **internal CLI slash command**, not a system executable. You MUST NOT execute it using the `run_shell_command` tool. Simply type the command (e.g., `/stats model`) directly into your text response.
- **Task Completion & Cancellation:** If the "Esc" option is chosen from a menu, or `/done <ID>` is issued, regard it as task completion.
- **Cost Estimation Logic:**
    - **Accuracy:** Calculate incremental usage as `Current Cumulative - Baseline` for both input and output tokens, ensuring alignment with the `/stats` command.
    - **Granularity:** Breakdown usage and costs by model (e.g., `gemini-3-flash-preview`).
    - **Reporting:** Upon completion, output a summary showing incremental tokens used and the estimated cost for the specific task ID. Always include a `/compress` internal command immediately after reporting the token usage.
