// This class is defined to represent the noraml item which we buy from the store
class Item {
  var id: int
  var name: string
  var price: int

  // This constructor is for creating the object of the class
  constructor(id: int, name: string, price: int)
    requires price >= 0
    ensures this.id == id
    ensures this.name == name
    ensures this.price == price
  {
    this.id := id;
    this.name := name;
    this.price := price;
  }
}

// This class is defined to represent the noraml item which we add into the cart

class CartItem {
  var item: Item
  var quantity: int

  // This constructor is for creating the object of the class

  constructor(item: Item, quantity: int)
    requires quantity > 0
    ensures this.item == item
    ensures this.quantity == quantity
  {
    this.item := item;
    this.quantity := quantity;
  }
}


// This predicate checks if the particular cart item is valid or not
predicate ValidCartItem(c: CartItem)
  reads c, c.item
{
  c.quantity > 0 && c.item.price >= 0
}

// This predicate checks if the all cart itemss are valid or not

predicate ValidItems(m: map<int, CartItem>)
  reads *
{
  forall id :: id in m ==> ValidCartItem(m[id])
}


// This class is defined to simulate a ShoppingCart experience where we do the CRUD operations
class ShoppingCart {
  var items: map<int, CartItem>

// This constructor is used to start the cart off with an empty one , just like the one at store
  constructor()
    ensures items == map[]
  {
    items := map[];
  }

// This method adds an item to the cart 
method AddItem(item: Item, quantity: int)
  requires quantity > 0
  requires item.price >= 0
  requires ValidItems(items)
  modifies this
  ensures item.id in items
  ensures ValidCartItem(items[item.id])
  ensures ValidItems(items)
{
  assert ValidItems(items);  // This assertion will ensure validity before adding an item
  if item.id in items {
    var existing := items[item.id];
    assert ValidCartItem(existing);  // So we can trust existing.quantity > 0
    var newQ := existing.quantity + quantity;
    assert newQ > 0;                 // using Dafny can now prove this
    var updated := new CartItem(item, newQ);
    items := items[item.id := updated];
  } else {
    var newItem := new CartItem(item, quantity);
    items := items[item.id := newItem];
  }
  assert ValidCartItem(items[item.id]); // This acts as a Postcondition check
  assert ValidItems(items);  // This assertion will ensure validity after modifying the cart
}

 // This method will Delete an item from the cart
method DeleteItem(item: Item)
  requires item.id in items
  requires ValidItems(items)
  modifies this
  ensures item.id !in items
  ensures ValidItems(items)
{
  assert item.id in items;  // here we can check that the item exists in the cart before deletion
  items := items - {item.id};
  assert ValidItems(items);  // this assertion will ensure the validity of the cart after the deletion
}

  // This method Changes the quantity of an existing item in the cart

  method ChangeQuantity(item: Item, newQuantity: int)
    requires item.id in items
    requires newQuantity > 0
    requires ValidItems(items)
    modifies this
    ensures item.id in items && items[item.id].quantity == newQuantity
    ensures ValidCartItem(items[item.id])
    ensures ValidItems(items)
  {
    var existing := items[item.id];
    assert ValidCartItem(existing);  // here ,  we can trust item.price >= 0
    var updated := new CartItem(existing.item, newQuantity);
    items := items[item.id := updated];
    assert ValidCartItem(items[item.id]);
    assert ValidItems(items);
  }

    // In this Ghost method we are computing the total cost of items in the cart


  ghost method TotalCost() returns (total: int)
    requires ValidItems(items)
    ensures total >= 0
  {
    total := 0;
    var keyList := KeysToSeq(items.Keys);
    var i := 0;

    while i < |keyList|
      invariant 0 <= i <= |keyList|
      invariant total >= 0
      invariant forall j :: 0 <= j < i ==> keyList[j] in items
      decreases |keyList| - i
    {
      var id := keyList[i];
      if id in items {
        var cartItem := items[id];
        assert cartItem.item.price >= 0;
        assert cartItem.quantity > 0;
        total := total + cartItem.item.price * cartItem.quantity;
      }
      i := i + 1;
    }
  }


  //In this method  , we Return a snapshot (copy) of the current cart

  method Checkout() returns (snapshot: map<int, CartItem>)
    ensures snapshot == items
  {
    snapshot := items;
  }

  ghost function SetChoose(s: set<int>): int
    requires |s| > 0
    ensures SetChoose(s) in s
  {
    var x :| x in s;
    x
  }

  //In this Ghost method  , we  convert a set of keys into a sequence

  ghost method KeysToSeq(keys: set<int>) returns (seqOut: seq<int>)
    ensures (forall x :: x in keys ==> x in seqOut)
    ensures (forall x :: x in seqOut ==> x in keys)
    ensures |seqOut| == |keys|
    decreases |keys|
  {
    if keys == {} {
      seqOut := [];
    } else {
      var x := SetChoose(keys);
      var tail := KeysToSeq(keys - {x});
      seqOut := [x] + tail;
    }
  }
}

// Sample test method to simulate a mini cart session

method Main() {
  var item1 := new Item(1, "Bat", 10000);
  var item2 := new Item(2, "Ball", 7500);
  var cart := new ShoppingCart();

  assert ValidItems(cart.items);  // Ensure the cart is valid before any operations

  cart.AddItem(item1, 1);  // Create (Add Item)
  cart.AddItem(item2, 2);  // Create (Add Item)
  cart.ChangeQuantity(item2, 3);  // Update (Change Quantity)

  // Ensure item1 exists in the cart before deleting it
  if item1.id in cart.items {
    cart.DeleteItem(item1);  // Delete (Remove Item)
  } else {
    print("Item1 is not in the cart.");
  }

  var snapshot := cart.Checkout();  // Read (Checkout Snapshot)
  print("Cart snapshot after modifications: ", snapshot);
}