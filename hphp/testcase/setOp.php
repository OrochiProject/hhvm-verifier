<?php

$multi1 = NULL;
$multi1 = add_multi($multi1, 1, 0);
$multi1 = add_multi($multi1, 4, 1);
$multi1 = add_multi($multi1, 7, 2);

$multi2 = NULL;
$multi2 = add_multi($multi2, 3, 0);
$multi2 = add_multi($multi2, 1, 1);
$multi2 = add_multi($multi2, 6, 2);

$a = 2;

print("Starting...\n");
print("multi1: ");
print($multi1);
print("\nmulti2: ");
print($multi2);
print("\na: ");
print($a);
print("\n");

print("multi1 += a: ");
$multi1 += $a;
print($multi1);
print("\n");

print("a += multi1: ");
$a += $multi1;
print($a);
print("\n");

print("multi1 += multi2: ");
$multi1 += $multi2;
print($multi1);
print("\n");
