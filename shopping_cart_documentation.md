# Shopping Cart System with Formal Verification in Dafny

## Overview

This document provides a comprehensive explanation of a shopping cart system implemented in Dafny with formal verification. The system models a typical e-commerce shopping cart where users can add items, delete items, change quantities, and check out. Dafny's verification features are used to ensure the system always maintains data integrity and behaves as expected.

## Key Components

### Item Class

Represents a product that can be added to the shopping cart.

```dafny
class Item {
  var id: int     // Unique identifier for the item
  var name: string // Name of the item
  var price: int   // Price in cents (avoids floating-point issues)
}
```

**Formal Verification:**
- Constructor requires `price >= 0` to ensure no negative prices
- Constructor ensures the fields are correctly initialized

### CartItem Class

Represents an item in the cart with its quantity.

```dafny
class CartItem {
  var item: Item    // Reference to the product
  var quantity: int // How many of this item are in the cart
}
```

**Formal Verification:**
- Constructor requires `quantity > 0` to ensure no zero or negative quantities
- Constructor ensures the fields are correctly initialized

### Predicates

Two predicates define what makes the cart data valid:

```dafny
predicate ValidCartItem(c: CartItem)
  reads c, c.item
{
  c.quantity > 0 && c.item.price >= 0
}

predicate ValidItems(m: map<int, CartItem>)
  reads *
{
  forall id :: id in m ==> ValidCartItem(m[id])
}
```

These predicates are used throughout the code to verify that:
1. All cart items have positive quantities
2. All items have non-negative prices
3. The entire cart maintains these invariants

### ShoppingCart Class

The main class that handles shopping cart operations.

#### Core Data Structure

```dafny
var items: map<int, CartItem>
```

The cart stores items in a map, with item IDs as keys and CartItem objects as values.

## Core Operations

### AddItem

Adds a new item to the cart or increases the quantity if the item already exists.

```dafny
method AddItem(item: Item, quantity: int)
  requires quantity > 0
  requires item.price >= 0
  requires ValidItems(items)
  modifies this
  ensures item.id in items
  ensures ValidCartItem(items[item.id])
  ensures ValidItems(items)
```

**Verification Properties:**
- Requires positive quantity and non-negative price
- Requires the cart to be valid before adding
- Ensures the item is in the cart after the operation
- Ensures the resulting cart item is valid
- Ensures the entire cart remains valid

### DeleteItem

Removes an item from the cart.

```dafny
method DeleteItem(item: Item)
  requires item.id in items
  requires ValidItems(items)
  modifies this
  ensures item.id !in items
  ensures ValidItems(items)
```

**Verification Properties:**
- Requires the item to exist in the cart
- Requires the cart to be valid before deletion
- Ensures the item is no longer in the cart after deletion
- Ensures the cart remains valid after the operation

### ChangeQuantity

Updates the quantity of an existing item.

```dafny
method ChangeQuantity(item: Item, newQuantity: int)
  requires item.id in items
  requires newQuantity > 0
  requires ValidItems(items)
  modifies this
  ensures item.id in items && items[item.id].quantity == newQuantity
  ensures ValidCartItem(items[item.id])
  ensures ValidItems(items)
```

**Verification Properties:**
- Requires the item to exist in the cart
- Requires the new quantity to be positive
- Requires the cart to be valid before the change
- Ensures the item remains in the cart with the updated quantity
- Ensures the updated cart item is valid
- Ensures the entire cart remains valid

### TotalCost

Calculates the total cost of all items in the cart.

```dafny
ghost method TotalCost() returns (total: int)
  requires ValidItems(items)
  ensures total >= 0
```

**Verification Properties:**
- This is a ghost method, used only for verification
- Requires the cart to contain valid items
- Ensures the total cost is non-negative
- Uses loop invariants to maintain verification during iteration

### Checkout

Creates a snapshot of the cart.

```dafny
method Checkout() returns (snapshot: map<int, CartItem>)
  ensures snapshot == items
```

**Verification Properties:**
- Ensures the returned snapshot is exactly the same as the current cart items

## Helper Functions

### SetChoose

A ghost function that picks an element from a set.

```dafny
ghost function SetChoose(s: set<int>): int
  requires |s| > 0
  ensures SetChoose(s) in s
```

### KeysToSeq

Converts a set of keys to a sequence, used in the TotalCost method.

```dafny
ghost method KeysToSeq(keys: set<int>) returns (seqOut: seq<int>)
  ensures (forall x :: x in keys ==> x in seqOut)
  ensures (forall x :: x in seqOut ==> x in keys)
  ensures |seqOut| == |keys|
  decreases |keys|
```

## Usage Example

The `Main` method demonstrates the CRUD operations:

```dafny
method Main() {
  var item1 := new Item(1, "Laptop", 100000);
  var item2 := new Item(2, "Mouse", 2500);
  var cart := new ShoppingCart();

  // Create
  cart.AddItem(item1, 1);
  cart.AddItem(item2, 2);

  // Update
  cart.ChangeQuantity(item2, 3);

  // Delete
  if item1.id in cart.items {
    cart.DeleteItem(item1);
  }

  // Read
  var snapshot := cart.Checkout();
}
```

## Formal Verification Techniques Used

### 1. Preconditions and Postconditions

Each method specifies:
- **Preconditions (requires)**: What must be true before the method can be called
- **Postconditions (ensures)**: What the method guarantees will be true after execution

### 2. Assertions

Strategic assertions help the verifier track important properties:

```dafny
assert ValidItems(items);  // Ensure validity before adding an item
assert ValidCartItem(existing);  // Verify existing cart item is valid
assert newQ > 0;  // Verify the new quantity is positive
```

### 3. Invariants

Loop invariants in `TotalCost` ensure properties hold throughout iteration:

```dafny
invariant 0 <= i <= |keyList|
invariant total >= 0
invariant forall j :: 0 <= j < i ==> keyList[j] in items
```

### 4. Predicates for Data Invariants

`ValidCartItem` and `ValidItems` define what it means for data to be valid.

## Benefits of Formal Verification

This implementation demonstrates several benefits of formal verification:

1. **Correctness Guarantees**: Dafny mathematically proves that the code satisfies its specifications.
2. **No Runtime Errors**: Verified code is free from runtime errors like null references or out-of-bounds access.
3. **Invariant Maintenance**: The system guarantees that important properties (like positive quantities) are always maintained.
4. **Documentation**: Specifications serve as precise documentation of expected behavior.
5. **Design by Contract**: The code follows a clear contract between caller and implementation.

## Conclusion

This shopping cart implementation uses Dafny's formal verification to ensure correctness at each operation. The combination of preconditions, postconditions, assertions, and invariants guarantees that the cart always maintains data integrity and behaves as expected under all conditions.
