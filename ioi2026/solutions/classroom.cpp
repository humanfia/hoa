#include "classroom.h"

#include <utility>
#include <vector>

namespace {

using Paper = std::vector<int>;
using Papers = std::vector<Paper>;

std::vector<int> recover_history(int N, int completed_rounds,
                                 const Papers& papers) {
    std::vector<int> answer(N, -1);
    if (completed_rounds == 0) {
        return answer;
    }

    const int latest = completed_rounds - 1;

    // Old records are interpreted by support.  A compressed anchor that was
    // frozen after its own round is a duplicate of a true literal fact.
    for (const Paper& paper : papers) {
        if (paper.size() != 2) {
            continue;
        }
        const int round = paper[0];
        const int student = paper[1];
        if (0 <= round && round < latest &&
            0 <= student && student < N) {
            answer[student] = round;
        }
    }

    std::vector<int> remaining;
    std::vector<int> position(N, -1);
    for (int student = 0; student < N; ++student) {
        if (answer[student] == -1) {
            position[student] = static_cast<int>(remaining.size());
            remaining.push_back(student);
        }
    }

    if (remaining.empty()) {
        return answer;
    }

    std::vector<int> multiplicity(N, 0);
    bool empty_set_marker = false;
    for (const Paper& paper : papers) {
        if (paper.size() != 2 || paper[0] != latest) {
            continue;
        }
        if (paper[1] == 63) {
            empty_set_marker = true;
        } else if (0 <= paper[1] && paper[1] < N) {
            ++multiplicity[paper[1]];
        }
    }

    if (empty_set_marker) {
        return answer;
    }

    std::vector<bool> survivor(N, false);
    const int remaining_count = static_cast<int>(remaining.size());
    for (int anchor = 0; anchor < N; ++anchor) {
        if (multiplicity[anchor] == 0) {
            continue;
        }
        const int anchor_position = position[anchor];
        for (int offset = 1; offset <= multiplicity[anchor]; ++offset) {
            int index = anchor_position - offset;
            if (index < 0) {
                index += remaining_count;
            }
            survivor[remaining[index]] = true;
        }
    }

    for (int student : remaining) {
        if (!survivor[student]) {
            answer[student] = latest;
        }
    }
    return answer;
}

std::vector<Paper> encode_latest(int round,
                                 const std::vector<int>& remaining,
                                 const std::vector<bool>& raised) {
    std::vector<Paper> records;
    bool any_raised = false;
    for (int student : remaining) {
        any_raised = any_raised || raised[student];
    }

    if (!any_raised) {
        if (!remaining.empty()) {
            records.push_back({round, 63});
            records.resize(remaining.size());
        }
        return records;
    }

    const int remaining_count = static_cast<int>(remaining.size());
    for (int index = 0; index < remaining_count; ++index) {
        const int student = remaining[index];
        if (raised[student]) {
            continue;
        }
        int offset = 1;
        while (!raised[remaining[(index + offset) % remaining_count]]) {
            ++offset;
        }
        records.push_back(
            {round, remaining[(index + offset) % remaining_count]});
    }
    return records;
}

}  // namespace

std::vector<std::vector<int>> process_step(
    int N, int M, int R,
    std::vector<int> T,
    std::vector<std::vector<int>> A) {
    (void)M;

    const std::vector<int> history = recover_history(N, R, A);
    std::vector<bool> raised(N, false);
    for (int student : T) {
        raised[student] = true;
    }

    std::vector<Paper> records;
    records.reserve(N - static_cast<int>(T.size()));
    std::vector<int> remaining;
    for (int student = 0; student < N; ++student) {
        if (history[student] == -1) {
            remaining.push_back(student);
        } else {
            records.push_back({history[student], student});
        }
    }

    std::vector<Paper> latest = encode_latest(R, remaining, raised);
    for (Paper& paper : latest) {
        records.push_back(std::move(paper));
    }

    int record_index = 0;
    for (int holder = 0; holder < N; ++holder) {
        if (!raised[holder]) {
            A[holder] = std::move(records[record_index]);
            ++record_index;
        }
    }
    return A;
}

std::vector<int> determine_steps(
    int N, int M,
    std::vector<std::vector<int>> A) {
    return recover_history(N, M, A);
}
