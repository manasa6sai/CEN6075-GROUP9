# CRUD Patterns in the Shopping Cart Implementation

This document explains how the shopping cart system implements the fundamental CRUD (Create, Read, Update, Delete) operations with formal verification guarantees.

## CRUD Overview

CRUD operations form the foundation of most data management systems:

- **Create**: Add new data to the system
- **Read**: Retrieve existing data from the system
- **Update**: Modify existing data in the system
- **Delete**: Remove data from the system

The shopping cart implementation provides formally verified implementations of all four operations.

## Create: Adding Items to the Cart

### The AddItem Method

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

### Create Pattern Implementation

The AddItem method creates new records in the cart in two ways:

1. **Pure Creation**: When the item doesn't already exist in the cart:
   ```dafny
   if item.id in items {
     // Update existing item (see Update section)
   } else {
     var newItem := new CartItem(item, quantity);
     items := items[item.id := newItem];
   }
   ```

2. **Create-or-Update Pattern**: The method intelligently handles both creating a new entry or updating an existing one in a single operation.

### Verification Guarantees for Creation

- **Non-negative Prices**: `requires item.price >= 0`
- **Positive Quantities**: `requires quantity > 0`
- **Successful Addition**: `ensures item.id in items`
- **Item Validity**: `ensures ValidCartItem(items[item.id])`
- **Cart Integrity**: `ensures ValidItems(items)`

## Read: Accessing Cart Data

### The Checkout Method

```dafny
method Checkout() returns (snapshot: map<int, CartItem>)
  ensures snapshot == items
```

### Read Pattern Implementation

The primary read operation returns a complete snapshot of the cart:
```dafny
snapshot := items;
```

### The TotalCost Method (Ghost)

For verification purposes, the system includes a ghost method that computes the total cost:

```dafny
ghost method TotalCost() returns (total: int)
  requires ValidItems(items)
  ensures total >= 0
```

This implements a computed read pattern using a loop to calculate an aggregate value:

```dafny
total := 0;
var keyList := KeysToSeq(items.Keys);
var i := 0;

while i < |keyList|
  // Loop invariants omitted for brevity
{
  var id := keyList[i];
  if id in items {
    var cartItem := items[id];
    total := total + cartItem.item.price * cartItem.quantity;
  }
  i := i + 1;
}
```

### Verification Guarantees for Reading

- **Snapshot Exactness**: `ensures snapshot == items`
- **Total Cost Non-negativity**: `ensures total >= 0`

## Update: Modifying Cart Items

### The ChangeQuantity Method

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

### Update Pattern Implementation

The ChangeQuantity method completely replaces a cart item with an updated version:

```dafny
var existing := items[item.id];
assert ValidCartItem(existing);
var updated := new CartItem(existing.item, newQuantity);
items := items[item.id := updated];
```

### AddItem's Update Functionality

The AddItem method also implements an update pattern when adding an item that already exists:

```dafny
var existing := items[item.id];
assert ValidCartItem(existing);
var newQ := existing.quantity + quantity;
assert newQ > 0;
var updated := new CartItem(item, newQ);
items := items[item.id := updated];
```

### Verification Guarantees for Updates

- **Item Existence**: `requires item.id in items`
- **Positive New Quantity**: `requires newQuantity > 0`
- **Quantity Updated**: `ensures items[item.id].quantity == newQuantity`
- **Item Validity After Update**: `ensures ValidCartItem(items[item.id])`
- **Cart Integrity After Update**: `ensures ValidItems(items)`

## Delete: Removing Items from the Cart

### The DeleteItem Method

```dafny
method DeleteItem(item: Item)
  requires item.id in items
  requires ValidItems(items)
  modifies this
  ensures item.id !in items
  ensures ValidItems(items)
```

### Delete Pattern Implementation

The DeleteItem method removes an item using the map subtraction operator:

```dafny
assert item.id in items;  // Verify item exists before deletion
items := items - {item.id};
assert ValidItems(items);  // Verify cart remains valid after deletion
```

### Safe Deletion in Main

The Main method demonstrates a safe deletion pattern by checking existence before deleting:

```dafny
if item1.id in cart.items {
  cart.DeleteItem(item1);
} else {
  print("Item1 is not in the cart.");
}
```

### Verification Guarantees for Deletion

- **Item Existence**: `requires item.id in items`
- **Successful Removal**: `ensures item.id !in items`
- **Cart Integrity After Deletion**: `ensures ValidItems(items)`

## Complete CRUD Example

The Main method demonstrates all CRUD operations:

```dafny
method Main() {
  var item1 := new Item(1, "Laptop", 100000);
  var item2 := new Item(2, "Mouse", 2500);
  var cart := new ShoppingCart();

  assert ValidItems(cart.items);  // Verify cart validity before operations

  // CREATE
  cart.AddItem(item1, 1);
  cart.AddItem(item2, 2);

  // UPDATE
  cart.ChangeQuantity(item2, 3);

  // DELETE
  if item1.id in cart.items {
    cart.DeleteItem(item1);
  }

  // READ
  var snapshot := cart.Checkout();
}
```

## Advanced CRUD Patterns

### 1. Atomic Updates

The update operations (AddItem and ChangeQuantity) use atomic updates with map assignments:

```dafny
items := items[item.id := updated];
```

This ensures that only the specific entry is modified while all other entries remain unchanged.

### 2. Defensive Programming

The implementation uses defensive programming with preconditions:

```dafny
requires item.id in items
requires newQuantity > 0
requires ValidItems(items)
```

These preconditions guarantee that operations are only performed when the necessary conditions are met.

### 3. Postcondition Contracts

Each method provides clear postcondition contracts:

```dafny
ensures item.id in items
ensures ValidCartItem(items[item.id])
ensures ValidItems(items)
```

These serve as guarantees to callers about what the method will accomplish.

### 4. Invariant Preservation

All operations preserve key data invariants:

```dafny
ensures ValidItems(items)
```

This ensures that the system maintains consistent and valid data throughout its lifecycle.

## Conclusion

The shopping cart implementation provides a formally verified implementation of all CRUD operations. By using Dafny's verification capabilities, it guarantees that:

1. Create operations add valid items to the cart
2. Read operations provide accurate data
3. Update operations maintain data integrity
4. Delete operations successfully remove items

These guarantees go beyond typical unit testing by providing mathematical proofs that the operations behave correctly under all circumstances.
