#include "monuments.h"

#include <algorithm>
#include <array>
#include <cstddef>
#include <queue>
#include <utility>
#include <vector>

namespace {

enum Kind : std::size_t {
  movable_negative,
  movable_positive,
  ancient_negative,
  ancient_positive,
  kind_count,
};

struct Monument {
  long long radius;
  Kind kind;
};

class WeightedIsotonicCost {
 public:
  explicit WeightedIsotonicCost(long long upper_bound)
      : upper_bound_(upper_bound) {}

  void add(long long value, long long weight) {
    const long long clipped = std::clamp(value, 0LL, upper_bound_);
    cost_ += weight * absolute_difference(value, clipped);

    breakpoints_.push({clipped, 2 * weight});
    long long remaining = weight;
    while (remaining > 0) {
      auto [coordinate, multiplicity] = breakpoints_.top();
      breakpoints_.pop();

      const long long taken = std::min(remaining, multiplicity);
      cost_ += taken * (coordinate - clipped);
      remaining -= taken;
      multiplicity -= taken;

      if (multiplicity > 0) {
        breakpoints_.push({coordinate, multiplicity});
      }
    }
  }

  long long cost() const { return cost_; }

 private:
  static long long absolute_difference(long long first, long long second) {
    return first >= second ? first - second : second - first;
  }

  long long upper_bound_;
  long long cost_ = 0;
  std::priority_queue<std::pair<long long, long long>> breakpoints_;
};

}  // namespace

long long get_cost(std::vector<int> X, std::vector<int> P) {
  const long long movable_count =
      static_cast<long long>(X.size() - P.size());

  std::vector<Monument> monuments;
  monuments.reserve(X.size());

  std::size_t ancient_pointer = 0;
  for (std::size_t index = 0; index < X.size(); ++index) {
    const bool ancient = ancient_pointer < P.size() &&
                         static_cast<std::size_t>(P[ancient_pointer]) == index;
    if (ancient) {
      ++ancient_pointer;
    }

    const long long coordinate = static_cast<long long>(X[index]);
    if (coordinate == 0) {
      continue;
    }

    const bool negative = coordinate < 0;
    const long long radius = negative ? -coordinate : coordinate;
    Kind kind;
    if (ancient) {
      kind = negative ? ancient_negative : ancient_positive;
    } else {
      kind = negative ? movable_negative : movable_positive;
    }
    monuments.push_back({radius, kind});
  }

  std::sort(monuments.begin(), monuments.end(),
            [](const Monument& first, const Monument& second) {
              return first.radius > second.radius;
            });

  struct Event {
    long long radius;
    long long negative_delta;
    long long positive_delta;
  };
  std::vector<Event> events;
  events.reserve(monuments.size());

  long long forced_count = 0;
  for (std::size_t begin = 0; begin < monuments.size();) {
    std::size_t end = begin;
    std::array<long long, kind_count> count{};
    while (end < monuments.size() &&
           monuments[end].radius == monuments[begin].radius) {
      ++count[monuments[end].kind];
      ++end;
    }

    const long long ancient_difference =
        count[ancient_positive] - count[ancient_negative];
    const long long forced_negative = std::max(0LL, ancient_difference);
    const long long forced_positive = std::max(0LL, -ancient_difference);
    forced_count += forced_negative + forced_positive;

    events.push_back({monuments[begin].radius,
                      count[movable_negative] - forced_negative,
                      count[movable_positive] - forced_positive});
    begin = end;
  }

  if (forced_count > movable_count) {
    return -1;
  }

  const long long pair_limit = (movable_count - forced_count) / 2;
  WeightedIsotonicCost regression(pair_limit);

  long long negative_surplus = 0;
  long long positive_surplus = 0;
  for (std::size_t index = 0; index < events.size(); ++index) {
    negative_surplus += events[index].negative_delta;
    positive_surplus += events[index].positive_delta;

    const long long next_radius =
        index + 1 < events.size() ? events[index + 1].radius : 0;
    const long long width = events[index].radius - next_radius;

    regression.add(std::max(negative_surplus, positive_surplus), width);
    regression.add(std::min(negative_surplus, positive_surplus), width);
  }

  return regression.cost();
}
