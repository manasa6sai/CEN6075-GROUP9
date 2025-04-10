using NUnit.Framework;
using _module;

[TestFixture]
public class CartTests
{
    [Test]
    public void TestValidCartItem_ValidItem_ReturnsTrue()
    {
        // Arrange
        var item = new Item();
        item.__ctor(1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Laptop"), new BigInteger(100));
        var cartItem = new CartItem();
        cartItem.__ctor(item, new BigInteger(2));

        // Act
        bool result = __default.ValidCartItem(cartItem);

        // Assert
        Assert.IsTrue(result);
    }

    [Test]
    public void TestValidCartItem_InvalidQuantity_ReturnsFalse()
    {
        // Arrange
        var item = new Item();
        item.__ctor(1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Laptop"), new BigInteger(100));
        var cartItem = new CartItem();
        cartItem.__ctor(item, new BigInteger(-1));  // Invalid quantity

        // Act
        bool result = __default.ValidCartItem(cartItem);

        // Assert
        Assert.IsFalse(result);
    }

    [Test]
    public void TestValidCartItem_InvalidPrice_ReturnsFalse()
    {
        // Arrange
        var item = new Item();
        item.__ctor(1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Laptop"), new BigInteger(-100));  // Invalid price
        var cartItem = new CartItem();
        cartItem.__ctor(item, new BigInteger(2));

        // Act
        bool result = __default.ValidCartItem(cartItem);

        // Assert
        Assert.IsFalse(result);
    }
}

[Test]
public void TestAddItem_NewItem_AddsToCart()
{
    // Arrange
    var item = new Item();
    item.__ctor(1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Laptop"), new BigInteger(100));
    var cart = new ShoppingCart();
    cart.__ctor();

    // Act
    cart.AddItem(item, new BigInteger(2));

    // Assert
    Assert.IsTrue(cart.items.Contains(item.id));  // Ensure item is added
}

[Test]
public void TestAddItem_ExistingItem_UpdatesQuantity()
{
    // Arrange
    var item = new Item();
    item.__ctor(1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Laptop"), new BigInteger(100));
    var cart = new ShoppingCart();
    cart.__ctor();
    cart.AddItem(item, new BigInteger(2));

    // Act
    cart.AddItem(item, new BigInteger(3));  // Update quantity

    // Assert
    var cartItem = Dafny.Map<BigInteger, CartItem>.Select(cart.items, item.id);
    Assert.AreEqual(cartItem.quantity, new BigInteger(5));  // Verify updated quantity
}
[Test]
public void TestDeleteItem_ItemExists_RemovesItem()
{
    // Arrange
    var item = new Item();
    item.__ctor(1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Laptop"), new BigInteger(100));
    var cart = new ShoppingCart();
    cart.__ctor();
    cart.AddItem(item, new BigInteger(2));

    // Act
    cart.DeleteItem(item);

    // Assert
    Assert.IsFalse(cart.items.Contains(item.id));  // Ensure item is removed
}
[Test]
public void TestChangeQuantity_ValidItem_UpdatesQuantity()
{
    // Arrange
    var item = new Item();
    item.__ctor(1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Laptop"), new BigInteger(100));
    var cart = new ShoppingCart();
    cart.__ctor();
    cart.AddItem(item, new BigInteger(2));

    // Act
    cart.ChangeQuantity(item, new BigInteger(5));  // Change quantity

    // Assert
    var cartItem = Dafny.Map<BigInteger, CartItem>.Select(cart.items, item.id);
    Assert.AreEqual(cartItem.quantity, new BigInteger(5));  // Verify updated quantity
}
[Test]
public void TestCheckout_ReturnsCartSnapshot()
{
    // Arrange
    var item1 = new Item();
    item1.__ctor(1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Laptop"), new BigInteger(100));
    var item2 = new Item();
    item2.__ctor(2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Mouse"), new BigInteger(25));
    var cart = new ShoppingCart();
    cart.__ctor();
    cart.AddItem(item1, new BigInteger(1));
    cart.AddItem(item2, new BigInteger(2));

    // Act
    var snapshot = cart.Checkout();

    // Assert
    Assert.AreEqual(snapshot.Count, 2);  // Verify the cart snapshot contains 2 items
}
