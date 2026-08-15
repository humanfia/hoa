#include "tiling.h"
#include <cassert>
#include <cstdio>
#include <vector>

int main() {
  int N, M;
  assert(2 == scanf("%d%d", &N, &M));

  std::vector<int> TL(N * M), TR(N * M), BL(N * M), BR(N * M);
  for (int k = 0; k < N * M; ++k) {
    assert(4 == scanf("%d%d%d%d", &TL[k], &TR[k], &BL[k], &BR[k]));
  }
  fclose(stdin);

  init(N, M);

  for (int k = 0; k < N * M; ++k) {
    auto [R, C] = receive_block(TL[k], TR[k], BL[k], BR[k]);
    printf("%d %d\n", R, C);
  }
  fclose(stdout);

  return 0;
}
