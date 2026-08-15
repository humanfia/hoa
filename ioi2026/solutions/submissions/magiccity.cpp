#include <algorithm>
#include <cassert>
#include <cstddef>
#include <utility>
#include <vector>

namespace {

struct IncidenceFamily {
    int block_count;
    std::vector<std::vector<int>> blocks_by_difference;
};

std::vector<std::vector<int>> small_block_differences(int k) {
    static const std::vector<std::vector<std::vector<int>>> tables = {
        {},
        {{1}},
        {{1, 3}, {1, 2}, {2, 3}},
        {{1, 3, 5}, {1, 2, 4}, {2, 4, 5}, {2, 3, 4}},
        {{1, 2, 6, 7},
         {1, 3, 4, 5},
         {3, 4, 5, 7},
         {2, 3, 4, 5},
         {3, 4, 5, 6}},
        {{1, 4, 5, 6, 9},
         {1, 2, 3, 7, 8},
         {2, 3, 7, 8, 9},
         {2, 4, 5, 6, 8},
         {3, 4, 5, 6, 7}},
    };
    return tables[static_cast<std::size_t>(k)];
}

void augment_periodic_family(int k,
                             std::vector<std::vector<int>>& incidence) {
    const int q = 2 * k;
    switch (k % 4) {
        case 0:
            std::swap(incidence[1], incidence[k]);
            incidence[k].push_back(4);
            incidence[2].push_back(2);
            incidence[q - 2].push_back(5);
            break;
        case 1:
            incidence[k].push_back(3);
            incidence[1].push_back(4);
            incidence[q - 1].push_back(5);
            break;
        case 2:
            incidence[k].push_back(2);
            incidence[3].push_back(4);
            incidence[q - 3].push_back(5);
            break;
        case 3:
            incidence[k].push_back(4);
            incidence[1].push_back(3);
            incidence[q - 1].push_back(5);
            break;
    }
}

IncidenceFamily make_incidence_family(int k) {
    const int q = 2 * k;
    std::vector<std::vector<int>> incidence(q);
    int block_count = 0;

    if (k <= 5) {
        const std::vector<std::vector<int>> rows = small_block_differences(k);
        block_count = static_cast<int>(rows.size());
        for (int block = 0; block < block_count; ++block) {
            for (const int difference : rows[block]) {
                incidence[difference].push_back(block);
            }
        }
    } else {
        constexpr int masks[4][3] = {
            {2, 4, 5},
            {0, 1, 2},
            {0, 3, 4},
            {1, 3, 5},
        };
        block_count = 6;
        for (int difference = 1; difference < q; ++difference) {
            for (const int block : masks[difference % 4]) {
                incidence[difference].push_back(block);
            }
        }
        augment_periodic_family(k, incidence);
    }

    for (std::vector<int>& blocks : incidence) {
        std::sort(blocks.begin(), blocks.end());
    }
    return {block_count, std::move(incidence)};
}

#ifndef NDEBUG
void assert_incidence_family(int k, const IncidenceFamily& family) {
    const int q = 2 * k;
    const std::vector<std::vector<int>>& incidence =
        family.blocks_by_difference;
    assert(static_cast<int>(incidence.size()) == q);
    assert(incidence[0].empty());

    std::vector<int> block_counts(family.block_count, 0);
    for (int difference = 1; difference < q; ++difference) {
        const std::vector<int>& blocks = incidence[difference];
        assert(!blocks.empty());
        assert(std::is_sorted(blocks.begin(), blocks.end()));
        assert(std::adjacent_find(blocks.begin(), blocks.end()) == blocks.end());
        assert(blocks.size() == incidence[q - difference].size());
        for (const int block : blocks) {
            assert(0 <= block && block < family.block_count);
            ++block_counts[block];
        }
    }

    for (int first = 1; first < q; ++first) {
        for (int second = 1; second < q; ++second) {
            bool intersects = false;
            for (const int block : incidence[first]) {
                intersects = intersects ||
                             std::binary_search(incidence[second].begin(),
                                                incidence[second].end(), block);
            }
            assert(intersects);
        }
    }
    for (const int count : block_counts) {
        assert(count == k);
    }
}
#endif

}  // namespace

std::pair<std::vector<int>, std::vector<std::pair<int, int>>> construct(int K) {
    assert(1 <= K && K <= 50);
    const int q = 2 * K;
    const IncidenceFamily family = make_incidence_family(K);
#ifndef NDEBUG
    assert_incidence_family(K, family);
#endif

    std::vector<int> types;
    types.reserve(static_cast<std::size_t>(family.block_count * q));
    for (int block = 0; block < family.block_count; ++block) {
        for (int type = 0; type < q; ++type) {
            types.push_back(type);
        }
    }

    std::vector<std::pair<int, int>> edges;
    edges.reserve(types.size() * static_cast<std::size_t>(K) / 2U);
    const std::vector<std::vector<int>>& incidence =
        family.blocks_by_difference;

    for (int difference = 1; difference < K; ++difference) {
        const std::vector<int>& first_blocks = incidence[difference];
        const std::vector<int>& second_blocks = incidence[q - difference];
        assert(first_blocks.size() == second_blocks.size());
        for (int type = 0; type < q; ++type) {
            int neighbor_type = type + difference;
            if (neighbor_type >= q) {
                neighbor_type -= q;
            }
            for (std::size_t index = 0; index < first_blocks.size(); ++index) {
                edges.emplace_back(first_blocks[index] * q + type,
                                   second_blocks[index] * q + neighbor_type);
            }
        }
    }

    for (const int block : incidence[K]) {
        for (int type = 0; type < K; ++type) {
            edges.emplace_back(block * q + type, block * q + type + K);
        }
    }

    assert(edges.size() == types.size() * static_cast<std::size_t>(K) / 2U);
    return {std::move(types), std::move(edges)};
}
