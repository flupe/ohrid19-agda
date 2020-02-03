int main () {
  int x = 2;
  int y = 3;

  if (x > 3) {
    y = 4;
  }
  else {
    y = 5;
  }

  do {
    x = x + 2;
  } while (y > x);

  switch (x) {
    case 6:
      x = 4;
      break;

    case 3:
      x = 9;
      break;
  }

  printInt x;
}
