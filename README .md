# Verified Shopping Cart System in Dafny

## Overview

This repository contains a formally verified implementation of a shopping cart system using the Dafny programming language. The implementation demonstrates how to use formal verification techniques to ensure correctness in a typical e-commerce component.

## Contents

This repository includes:

1. **[shopping_cart.dfy](shopping_cart.dfy)** - The Dafny implementation of the shopping cart system with formal verification
2. **[shopping_cart_documentation.md](shopping_cart_documentation.md)** - Comprehensive documentation of the implementation
3. **[shopping_cart_verification_details.md](shopping_cart_verification_details.md)** - Technical details of the formal verification approach
4. **[shopping_cart_crud_patterns.md](shopping_cart_crud_patterns.md)** - Explanation of the CRUD patterns implemented in the system

## Key Features

- Complete implementation of a shopping cart with add, delete, change quantity, and checkout operations
- Formal verification guaranteeing data integrity and correct behavior
- CRUD (Create, Read, Update, Delete) operations with verification guarantees
- Ghost methods for expressing properties about the system
- Predicates to define what makes the data valid

## Verification Properties

The implementation verifies several key properties:

1. **Quantity Positivity**: Cart items always have positive quantities
2. **Price Non-negativity**: Item prices are never negative
3. **Cart Validity**: The cart remains in a valid state after every operation
4. **Total Cost Correctness**: The total cost is always correctly calculated and non-negative
5. **Data Integrity**: Operations like adding, removing, and changing quantities maintain data integrity

## Usage

### Prerequisites

To run and verify this code, you'll need:

- [Dafny](https://github.com/dafny-lang/dafny) installed on your system
- Familiarity with basic formal verification concepts

### Running the Code

1. Clone this repository
2. Verify the implementation with: `dafny /verify Group9DafnySpecification.dfy`
3. Run the implementation with: `dafny /compile:3 /run Group9DafnySpecification.dfy`

## Documentation

See the following documentation files for more details:

- [Comprehensive Documentation](shopping_cart_documentation.md)
- [Verification Details](shopping_cart_verification_details.md)
- [CRUD Patterns](shopping_cart_crud_patterns.md)

## License

This project is available under the MIT License.

## Acknowledgments

- The Dafny team for creating a powerful formal verification language
- The formal methods community for advancing the field of software verification
