#include <algorithm>
#include <cstdint>
#include <numeric>
#include <vector>

namespace {

using i128 = __int128_t;

int block_count(const std::vector<i128>& weight, i128 capacity, int stop_after) {
    int blocks = 1;
    i128 current = 0;
    for (i128 value : weight) {
        if (current + value > capacity) {
            ++blocks;
            current = 0;
            if (blocks > stop_after) {
                return blocks;
            }
        }
        current += value;
    }
    return blocks;
}

class PredecessorSet {
public:
    explicit PredecessorSet(int size) : parent_(size + 1) {
        std::iota(parent_.begin(), parent_.end(), 0);
    }

    int find(int node) {
        int root = node;
        while (parent_[root] != root) {
            root = parent_[root];
        }
        while (parent_[node] != node) {
            const int next = parent_[node];
            parent_[node] = root;
            node = next;
        }
        return root;
    }

    void erase(int node) {
        parent_[node] = find(node - 1);
    }

private:
    std::vector<int> parent_;
};

}  // namespace

std::vector<int> add_numbers(std::vector<int> A, int K, int M) {
    (void)M;
    std::sort(A.begin(), A.end());

    const int n = static_cast<int>(A.size());
    const i128 residue_sum = static_cast<i128>(n) * (n + 1) / 2;
    const i128 base = residue_sum + n + 1;

    std::vector<i128> weight(n);
    i128 low = 0;
    i128 high = 0;
    for (int i = 0; i < n; ++i) {
        weight[i] = static_cast<i128>(A[i]) * base + (i + 1);
        low = std::max(low, weight[i]);
        high += weight[i];
    }

    while (low < high) {
        const i128 middle = low + (high - low) / 2;
        if (block_count(weight, middle, K) <= K) {
            high = middle;
        } else {
            low = middle + 1;
        }
    }

    const i128 capacity = low;
    const std::int64_t target = static_cast<std::int64_t>(capacity / base);
    std::vector<int> additions;
    std::int64_t ordinary_sum = 0;
    i128 perturbed_sum = 0;
    int blocks = 1;

    for (int i = 0; i < n; ++i) {
        if (perturbed_sum + weight[i] > capacity) {
            const std::int64_t deficit = target - ordinary_sum;
            if (deficit > 0) {
                additions.push_back(static_cast<int>(deficit));
            }
            ++blocks;
            ordinary_sum = 0;
            perturbed_sum = 0;
        }
        ordinary_sum += A[i];
        perturbed_sum += weight[i];
    }

    const std::int64_t final_deficit = target - ordinary_sum;
    if (final_deficit > 0) {
        additions.push_back(static_cast<int>(final_deficit));
    }
    while (blocks < K) {
        additions.push_back(static_cast<int>(target));
        ++blocks;
    }
    return additions;
}

std::vector<int> find_partition(std::vector<int> B, int K) {
    const std::int64_t total =
        std::accumulate(B.begin(), B.end(), std::int64_t{0});
    const std::int64_t target = total / K;

    const int size = static_cast<int>(B.size());
    PredecessorSet unused(size);
    std::vector<int> label(size, -1);

    for (int group = 0; group < K; ++group) {
        std::int64_t remaining = target;
        while (remaining > 0) {
            const int limit = static_cast<int>(
                std::upper_bound(B.begin(), B.end(), remaining) - B.begin());
            const int node = unused.find(limit);
            const int index = node - 1;
            label[index] = group;
            remaining -= B[index];
            unused.erase(node);
        }
    }
    return label;
}
