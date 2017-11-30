<?php

$int = NULL;
$int = add_multi($int, 1, 1);
$int = add_multi($int, 2, 2);

$result = ~$int;
print("BitNot: ");
print($result);
print("\n");

$result = (bool)$int;
print("CastBool: ");
print($result);
print("\n");

$result = (double)$int;
print("CastDouble: ");
print($result);
print("\n");

$result = (int)$int;
print("CastInt: ");
print($result);
print("\n");

print("CastObject: ");
print($result);
print("\n");

$result = (string)$int;
print("CastString: ");
print($result);
print("\n");

$result = !$int;
print("Not: ");
print($result);
print("\n");

print("Original: ");
print($int);
print("\n");
