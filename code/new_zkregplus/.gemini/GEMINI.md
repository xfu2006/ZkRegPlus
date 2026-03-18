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

# Task Tracking & Cost Estimation Rules
When I run `/mytask <id>`, you must remember the current token counts.
When I run `/done <id>`, you must perform the following calculation:
- **Input Cost:** (Current Input - Baseline Input) * Price per 1k
- **Output Cost:** (Current Output - Baseline Output) * Price per 1k

### Pricing Reference (USD per 1M tokens)
| Model              | Input ($) | Output ($) |
|--------------------|-----------|------------|
| Gemini 1.5 Pro     | 1.25      | 5.00       |
| Gemini 1.5 Flash   | 0.075     | 0.30       |
| Gemini 2.0 Flash   | 0.10      | 0.40       |
| Gemini 3.1 Pro	 | 2.00		 | 12.00      |
| Gemini 3.1 Flash	 |0.50		 | 3.00       |
| Gemini 3.0 Pro	 |1.25		 | 10.00      |
| Gemini 3.0 Flash	 |0.30		 | 2.50       |
| Gemini 2.5 Pro	 |1.00		 | 8.00       |
| Gemini 2.5 Flash	 |0.15		 | 0.60		  |
| Gemini 2.5 Flash-Lite	| 0.10	 | 0.40       |
| Gemini 2.0 Flash	| 0.10		 | 0.40       |
| Gemini 2.0 Flash-Lite	| 0.075	 | 0.30       |

### Output Format for /done:
**Task:** <id>
**Summary:** <brief_description>
**Usage Delta:** <input_tokens> input / <output_tokens> output
**Estimated Cost:** $<total_cost>
