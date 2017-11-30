<?php

class TestObj {
  public $val1 = 1;
  public $val2 = 2;
  public function __construct($val1, $val2) {
    $this->val1 = $val1;
    $this->val2 = $val2;
  }
  public function __toString() {
    return "val1: {$this->val1}, val2: {$this->val2}";
  }
  public function addOne() {
    $this->val1 = $this->val1 + 1;
    $this->val2 = $this->val2 + 1;
  }
}

$obj = new TestObj(1, 2);
$obj2 = new TestObj(3, 4);

$multi = NULL;
$multi = add_multi($multi, $obj, 1);
$multi = add_multi($multi, $obj2, 2);

print("TestObj: ");
print($multi);
print("\n");

print("Cloning...\n");
$multi2 = clone $multi;

print("TestObj: ");
print($multi);
print("\n");

print("CloneObj: ");
print($multi2);
print("\n");
