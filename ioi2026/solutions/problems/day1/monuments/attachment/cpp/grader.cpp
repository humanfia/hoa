#include "monuments.h"
#include <cassert>
#include <cstdio>

int main() {
  int N, M;
  assert(2 == scanf("%d %d", &N, &M));

  std::vector<int> X(N);
  for (int i = 0; i < N; i++) {
    assert(1 == scanf("%d", &X[i]));
  }

  std::vector<int> P(M);
  for (int i = 0; i < M; i++) {
    assert(1 == scanf("%d", &P[i]));
  }
  fclose(stdin);

  long long res = get_cost(X, P);

  printf("%lld\n", res);
  fclose(stdout);
  return 0;
}
