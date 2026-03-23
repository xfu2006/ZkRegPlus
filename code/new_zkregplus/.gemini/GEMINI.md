## Context Management & Token Optimization
- **Token Efficiency:** Keep tool outputs minimal. When editing code, provide only targeted, surgical code edits. Avoid rewriting entire files or printing out unmodified code.
- **Usage Warnings:** Proactively warn the user if a request requires processing massive amounts of data or generating excessive tokens (e.g., reading large directories, massive logs). Monitor the session and alert the user approximately every time an additional 1 million input or output tokens are consumed.
- **Limit Errors:** Ensure the full details of any model limit or quota errors are clearly communicated to the user immediately.

## Rust & Cryptography Project Guidelines
- **Libraries:** This project utilizes `arkworks`. Prioritize these libraries for cryptographic primitives, finite fields, algebraic curves, and zero-knowledge proofs over alternatives.
- **Tooling:** Always use standard `cargo` tooling (`cargo check`, `cargo build`, `cargo clippy`) for validation. When fixing compiler or clippy errors, provide minimal and precise fixes. Do not run Cargo test
- **Style:** Adhere strictly to standard Rust idioms, safety practices, and formatting. Do not introduce unsafe blocks unless explicitly required and justified.

- **Code Insertion:** Whenever inserting or modifying code, ensure the line width does not exceed 80 characters. Maintain consistency with the project's existing coding style and formatting.

# .gemini configuration for Structured Coding Workflow
commands:
  plan:
    description: "Enter research mode to analyze a task and summarize a strategy."
    rules:
      - Restriction: Do NOT modify any existing source code files.
      - Action: Use search/read tools to understand the codebase.
      	Write all technical details, including code changes in `diff` format, into a single file named `implementation_plan.md` in the project's root directory. This is the mandated location for plan files and overrides any other requests for different locations.
      - Output: Provide a high-level summary of the required logic and architectural changes.


  replan:
    description: "Read the modified plan file and update the strategy."
    rules:
      - Action: Read the current `implementation_plan.md` and incorporate the user's `desc` (provided as comments).
      - Action: Rewrite the `implementation_plan.md` with the updated details in the project's temporary directory. This is the mandated location for plan files and overrides any other requests for different locations.
      - Output: Provide a new summary of the revised plan.

  execute:
    description: "Execute the changes defined in the plan file with manual approval."
    rules:
      - Action: Parse `implementation_plan.md`.
      - Batching: Group all changes belonging to the same file together.
      - Approval Gate: Present all changes for `File A`. Wait for explicit user approval before applying changes to `File A`. Only then move to `File B`.
      - Finality: Ensure every item in the plan is addressed.

system_constraints:
  - "While in /plan, or /replan, any tool call that attempts to 'write' or 'edit' a non-plan file must be blocked."
  - "While in /plan, or /replan modes, do NOT use code modification tools (e.g., 'replace', 'write_file') or request user approval for code changes. These modes are strictly for read-only analysis, strategy summarization, and rewriting the plan file."
  - "Always prioritize the contents of `implementation_plan.md` as the source of truth during the /execute phase."

