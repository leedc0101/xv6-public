#include "types.h"
#include "user.h"
#include "stat.h"

int main()
{
  ps(0);

  printf(1, "\nsetting nice value 20 -> 10...\n");
  setnice(1, 10);

  printf(1, "\n");
  ps(0);

  printf(1, "\nsetting invalid nice value...\n");
  setnice(1, -2);

  printf(1, "\n");
  ps(0);

  printf(1, "\ngetnice with invalid pid value -2...\n");
  getnice(-2);

  printf(1, "\n");

  printf(1, "\ngetnice with invalid pid value 10...\n");
  getnice(10);

  printf(1, "\nps with valid pid value 4...\n");
  ps(2);

  printf(1, "\nps with invalid pid value 4...\n");
  ps(9);

  exit();
}