#include <utility>
#include <vector>

namespace {

int top_nonfull_row;
int bottom_nonfull_row;
std::vector<int> left_free;
std::vector<int> right_free;

void discard_full_frontier_rows() {
  while (top_nonfull_row <= bottom_nonfull_row &&
         left_free[top_nonfull_row] > right_free[top_nonfull_row]) {
    ++top_nonfull_row;
  }
  while (top_nonfull_row <= bottom_nonfull_row &&
         left_free[bottom_nonfull_row] > right_free[bottom_nonfull_row]) {
    --bottom_nonfull_row;
  }
}

}  // namespace

void init(int N, int M) {
  top_nonfull_row = 0;
  bottom_nonfull_row = N - 1;
  left_free.assign(N, 0);
  right_free.assign(N, M - 1);
}

std::pair<int, int> receive_block(int TL, int TR, int BL, int BR) {
  const int colors[4] = {TL, TR, BL, BR};
  int white_corner = 0;
  while (white_corner < 3 && colors[white_corner] != 0) {
    ++white_corner;
  }

  const bool white_is_bottom = white_corner >= 2;
  const bool white_is_right = (white_corner % 2) == 1;
  const int row =
      white_is_bottom ? top_nonfull_row : bottom_nonfull_row;

  int col;
  if (white_is_right) {
    col = left_free[row];
    ++left_free[row];
  } else {
    col = right_free[row];
    --right_free[row];
  }

  discard_full_frontier_rows();
  return {2 * row, 2 * col};
}
