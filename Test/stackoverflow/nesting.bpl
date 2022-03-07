// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo(n: int)
  requires true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true
  || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true ||
  true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true
    || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true ||
    true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true
      || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true ||
      true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true
        || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true ||
        true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true
          || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true ||
          true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true
            || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true ||
            n == 2;
{
  if (n == 2) {
    if (n == 2) {
      if (n == 2) {
        if (n == 2) {
          if (n == 2) {
            if (n == 2) {
              if (n == 2) {
                if (n == 2) {
                  if (n == 2) {
                    if (n == 2) {
                      if (n == 2) {
                        if (n == 2) {
                          if (n == 2) {
                            if (n == 2) {
                              if (n == 2) {
                                if (n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2  ) {
                                  assert n == 3;
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}
