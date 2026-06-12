Create a plan with name doc/fields/HMAC.md in the following order:

### 1. Mathematical Foundations for SHA-1, SHA-256, SHA-384, and SHA-512 Specifications

Define the necessary mathematical foundations—including definitions, lemmas, properties, and fundamental theorems—to formally specify the SHA-1, SHA-256, SHA-384, and SHA-512 functions (referencing FIPS 180-2 with change notice, `doc/field/fips180-2withchangenotice.pdf`) corresponding to the Rust functions `hmac_sha1`, `hmac_sha2_256`, `hmac_sha2_384`, and `hmac_sha2_512`.

The goal is to formulate the richest possible specification theorems, including:

* Formal definitions of bitwise operations, words, modular arithmetic, padding, message parsing, compression functions, constants, and digest generation.
* Supporting lemmas and algebraic properties required for mechanized verification.
* Fundamental correctness theorems linking the executable Rust implementation to the mathematical SHA specifications.
* Explicit treatment of output size, determinism, padding invariants, block decomposition, intermediate state evolution, and digest correctness.

This step should also provide:

* A detailed mathematical dependency hierarchy.
* A precise, step-by-step implementation strategy.
* Exact file and directory locations.
* A complete tree diagram of the proposed project structure.

### 2. Mathematical Foundations for the Structural HMAC Model

Building upon Step 1, define the necessary mathematical foundations—including definitions, lemmas, properties, and fundamental theorems—to formally specify the structural model of HMAC (referencing RFC 2104 and FIPS 198-1) corresponding to the Rust `hmac` function.

The objective is to formulate the richest possible specification theorems, including:

* Formalization of the HMAC construction:

  `H((K ⊕ opad) ∥ H((K ⊕ ipad) ∥ m))`

* Definitions of key normalization, block-size-dependent padding, inner/outer keyed hashing, and tag truncation behavior.

* Mathematical properties of XOR-based key transformation and compositional correctness.

* Fundamental theorems establishing correctness of the HMAC construction with respect to the underlying hash function specifications developed in Step 1.

* Rich behavioral guarantees such as determinism, output-length correctness, structural decomposition, and compatibility across SHA-1/SHA-2 variants.

This step should also provide:

* A detailed mathematical dependency hierarchy.
* A precise, step-by-step formal implementation plan.
* Exact file and directory locations.
* A complete tree diagram of the proposed project structure.

### 3. Integration with `Plan_authenticator`

The final step is to connect the mathematical specifications and correctness theorems developed in Steps 1 and 2 to the functions implemented in `Plan_authenticator`.

This stage should include:

* A precise refinement path from mathematical models to executable Rust functions.
* Specification theorems for the authenticator pipeline.
* End-to-end correctness guarantees linking implementation behavior to the formal SHA and HMAC specifications.
* Exact file and directory locations.
* A detailed tree diagram showing the integration structure and dependency flow.

Each step must include the necessary mathematical background, explicit conceptual dependencies, and a clear, step-by-step implementation roadmap using well-defined formal concepts.
