#include "ballmachine.h"

#include <algorithm>
#include <cstddef>
#include <numeric>
#include <utility>
#include <vector>

namespace {

struct Parameters {
  int nonsingleton_count = 0;
  int singleton_count = 0;
  int row_count = 0;
  int column_count = 0;
  int batch_width = 0;
  int batch_count = 0;
  int continuation_value = 0;
  std::vector<int> nonsingletons;
  std::vector<int> singletons;
  std::vector<int> nonsingleton_rank;
  std::vector<int> singleton_rank;
};

int ceiling_square_root(int value) {
  int root = 0;
  while (root * root < value) {
    ++root;
  }
  return root;
}

Parameters make_parameters(const std::vector<int> &length) {
  const int leaf_count = static_cast<int>(length.size());
  Parameters parameters;
  parameters.nonsingleton_rank.assign(static_cast<std::size_t>(leaf_count),
                                      -1);
  parameters.singleton_rank.assign(static_cast<std::size_t>(leaf_count), -1);

  for (int leaf = 0; leaf < leaf_count; ++leaf) {
    if (length[static_cast<std::size_t>(leaf)] == 1) {
      parameters.singleton_rank[static_cast<std::size_t>(leaf)] =
          static_cast<int>(parameters.singletons.size());
      parameters.singletons.push_back(leaf);
    } else {
      parameters.nonsingleton_rank[static_cast<std::size_t>(leaf)] =
          static_cast<int>(parameters.nonsingletons.size());
      parameters.nonsingletons.push_back(leaf);
    }
  }

  parameters.nonsingleton_count =
      static_cast<int>(parameters.nonsingletons.size());
  parameters.singleton_count =
      static_cast<int>(parameters.singletons.size());
  parameters.row_count =
      ceiling_square_root(parameters.nonsingleton_count);
  parameters.column_count =
      (parameters.nonsingleton_count + parameters.row_count - 1) /
      parameters.row_count;
  if (parameters.singleton_count == 0) {
    parameters.batch_width = 0;
    parameters.batch_count = 1;
  } else {
    parameters.batch_width =
        ceiling_square_root(parameters.singleton_count);
    parameters.batch_count =
        (parameters.singleton_count + parameters.batch_width - 1) /
        parameters.batch_width;
  }
  parameters.continuation_value =
      parameters.batch_width + parameters.row_count + 1;
  return parameters;
}

int marker_value(const Parameters &parameters,
                 const std::vector<int> &length, int leaf, int batch,
                 int successful) {
  const int component_length = length[static_cast<std::size_t>(leaf)];
  if (successful >= component_length) {
    return 0;
  }
  if (component_length == 1) {
    const int rank =
        parameters.singleton_rank[static_cast<std::size_t>(leaf)];
    const int first = batch * parameters.batch_width;
    if (first <= rank && rank < first + parameters.batch_width) {
      return rank - first + 1;
    }
    return 0;
  }

  const int rank =
      parameters.nonsingleton_rank[static_cast<std::size_t>(leaf)];
  const int first_digit = rank % parameters.row_count;
  const int second_digit = rank / parameters.row_count;
  if (successful == 0) {
    return parameters.batch_width + 1 + first_digit;
  }
  if (successful + 1 == component_length) {
    return parameters.continuation_value + 1 + second_digit;
  }
  return parameters.continuation_value;
}

struct ParsedComponent {
  bool singleton = false;
  int singleton_token = -1;
  int first_digit = -1;
  int second_digit = -1;
  std::vector<int> chain_nodes;
};

struct ParsedView {
  std::vector<ParsedComponent> components;
  std::vector<int> parent_node;
  std::vector<int> component_of_node;
  std::vector<int> chain_position;
  int root_component = -1;
};

class ViewParser {
public:
  ViewParser(const std::vector<int> &tokens, const Parameters &parameters)
      : tokens_(tokens), parameters_(parameters) {}

  bool parse(ParsedView &result) {
    if (tokens_.empty()) {
      return false;
    }
    if (!start_component(-1)) {
      return false;
    }
    view_.root_component = 0;

    while (!stack_.empty()) {
      if (position_ == tokens_.size()) {
        return false;
      }
      const int token = tokens_[position_];
      if (token < parameters_.continuation_value) {
        const int parent = stack_.back().current_node;
        if (!start_component(parent)) {
          return false;
        }
        continue;
      }

      ++position_;
      Frame &frame = stack_.back();
      if (token == parameters_.continuation_value) {
        frame.current_node = add_node(frame.component, frame.current_node);
        continue;
      }
      if (token < parameters_.continuation_value + 1 ||
          token > parameters_.continuation_value +
                      parameters_.column_count) {
        return false;
      }
      ParsedComponent &component =
          view_.components[static_cast<std::size_t>(frame.component)];
      component.second_digit =
          token - parameters_.continuation_value - 1;
      static_cast<void>(add_node(frame.component, frame.current_node));
      stack_.pop_back();
    }

    if (position_ != tokens_.size()) {
      return false;
    }
    result = std::move(view_);
    return true;
  }

private:
  struct Frame {
    int component = -1;
    int current_node = -1;
  };

  int add_node(int component, int parent) {
    const int node = static_cast<int>(view_.parent_node.size());
    view_.parent_node.push_back(parent);
    view_.component_of_node.push_back(component);
    const int position = static_cast<int>(
        view_.components[static_cast<std::size_t>(component)]
            .chain_nodes.size());
    view_.chain_position.push_back(position);
    view_.components[static_cast<std::size_t>(component)]
        .chain_nodes.push_back(node);
    return node;
  }

  bool start_component(int parent) {
    if (position_ == tokens_.size()) {
      return false;
    }
    const int token = tokens_[position_++];
    const int component = static_cast<int>(view_.components.size());
    if (0 <= token && token <= parameters_.batch_width) {
      view_.components.push_back(
          ParsedComponent{true, token, -1, -1, {}});
      static_cast<void>(add_node(component, parent));
      return true;
    }
    if (token < parameters_.batch_width + 1 ||
        token > parameters_.batch_width + parameters_.row_count) {
      return false;
    }
    view_.components.push_back(ParsedComponent{
        false, -1, token - parameters_.batch_width - 1, -1, {}});
    const int node = add_node(component, parent);
    stack_.push_back({component, node});
    return true;
  }

  const std::vector<int> &tokens_;
  const Parameters &parameters_;
  std::size_t position_ = 0;
  ParsedView view_;
  std::vector<Frame> stack_;
};

bool identify_components(const ParsedView &view,
                         const Parameters &parameters,
                         const std::vector<int> &length, int batch,
                         std::vector<int> &owner) {
  const int leaf_count = static_cast<int>(length.size());
  if (view.components.size() != static_cast<std::size_t>(leaf_count)) {
    return false;
  }
  owner.assign(view.components.size(), -1);
  std::vector<bool> seen(static_cast<std::size_t>(leaf_count), false);

  for (int component = 0;
       component < static_cast<int>(view.components.size()); ++component) {
    const ParsedComponent &record =
        view.components[static_cast<std::size_t>(component)];
    int identified = -1;
    if (!record.singleton) {
      const int rank =
          record.second_digit * parameters.row_count + record.first_digit;
      if (record.second_digit < 0 || rank < 0 ||
          rank >= parameters.nonsingleton_count) {
        return false;
      }
      identified =
          parameters.nonsingletons[static_cast<std::size_t>(rank)];
      if (record.chain_nodes.size() !=
          static_cast<std::size_t>(
              length[static_cast<std::size_t>(identified)])) {
        return false;
      }
    } else {
      if (record.chain_nodes.size() != 1U) {
        return false;
      }
      if (record.singleton_token != 0) {
        const int rank = batch * parameters.batch_width +
                         record.singleton_token - 1;
        if (rank < 0 || rank >= parameters.singleton_count) {
          return false;
        }
        identified =
            parameters.singletons[static_cast<std::size_t>(rank)];
      }
    }
    if (identified != -1) {
      if (seen[static_cast<std::size_t>(identified)]) {
        return false;
      }
      seen[static_cast<std::size_t>(identified)] = true;
      owner[static_cast<std::size_t>(component)] = identified;
    }
  }

  for (int leaf : parameters.nonsingletons) {
    if (!seen[static_cast<std::size_t>(leaf)]) {
      return false;
    }
  }
  const int first = batch * parameters.batch_width;
  const int limit =
      std::min(parameters.singleton_count, first + parameters.batch_width);
  for (int rank = first; rank < limit; ++rank) {
    const int leaf = parameters.singletons[static_cast<std::size_t>(rank)];
    if (!seen[static_cast<std::size_t>(leaf)]) {
      return false;
    }
  }
  return view.root_component >= 0 &&
         owner[static_cast<std::size_t>(view.root_component)] == 0;
}

struct Attachment {
  int parent_owner = -1;
  int chain_position = -1;
  bool seen = false;
};

bool absorb_view(const std::vector<int> &tokens,
                 const Parameters &parameters,
                 const std::vector<int> &length, int node_count, int batch,
                 std::vector<Attachment> &attachments) {
  ParsedView view;
  if (!ViewParser(tokens, parameters).parse(view) ||
      view.parent_node.size() != static_cast<std::size_t>(node_count)) {
    return false;
  }
  std::vector<int> owner;
  if (!identify_components(view, parameters, length, batch, owner)) {
    return false;
  }

  for (int component = 0;
       component < static_cast<int>(view.components.size()); ++component) {
    const int identified = owner[static_cast<std::size_t>(component)];
    if (identified <= 0) {
      continue;
    }
    const int root_node =
        view.components[static_cast<std::size_t>(component)]
            .chain_nodes.front();
    const int parent_node =
        view.parent_node[static_cast<std::size_t>(root_node)];
    if (parent_node < 0) {
      return false;
    }
    const int parent_component =
        view.component_of_node[static_cast<std::size_t>(parent_node)];
    const int parent_owner =
        owner[static_cast<std::size_t>(parent_component)];
    if (parent_owner < 0 ||
        view.components[static_cast<std::size_t>(parent_component)]
            .singleton) {
      return false;
    }
    const int position =
        view.chain_position[static_cast<std::size_t>(parent_node)];
    if (position < 0 ||
        position + 1 >=
            length[static_cast<std::size_t>(parent_owner)]) {
      return false;
    }

    Attachment &attachment =
        attachments[static_cast<std::size_t>(identified)];
    if (attachment.seen) {
      if (attachment.parent_owner != parent_owner ||
          attachment.chain_position != position) {
        return false;
      }
    } else {
      attachment = {parent_owner, position, true};
    }
  }
  return true;
}

std::vector<int> build_parent_array(const std::vector<int> &length,
                                    const std::vector<Attachment> &attachments,
                                    int node_count) {
  const int leaf_count = static_cast<int>(length.size());
  std::vector<std::vector<int>> label(static_cast<std::size_t>(leaf_count));
  int next_internal = leaf_count;
  for (int owner = 0; owner < leaf_count; ++owner) {
    const int component_length = length[static_cast<std::size_t>(owner)];
    label[static_cast<std::size_t>(owner)].resize(
        static_cast<std::size_t>(component_length));
    for (int position = 0; position < component_length; ++position) {
      int assigned = -1;
      if (position + 1 == component_length) {
        assigned = owner;
      } else if (owner == 0 && position == 0) {
        assigned = node_count - 1;
      } else {
        assigned = next_internal++;
      }
      label[static_cast<std::size_t>(owner)]
           [static_cast<std::size_t>(position)] = assigned;
    }
  }
  if (next_internal != node_count - 1) {
    return {};
  }

  std::vector<int> parent(static_cast<std::size_t>(node_count - 1), -1);
  for (int owner = 0; owner < leaf_count; ++owner) {
    const std::vector<int> &chain = label[static_cast<std::size_t>(owner)];
    if (owner != 0) {
      const Attachment &attachment =
          attachments[static_cast<std::size_t>(owner)];
      if (!attachment.seen || attachment.parent_owner < 0 ||
          attachment.parent_owner >= owner || attachment.chain_position < 0 ||
          attachment.chain_position + 1 >=
              length[static_cast<std::size_t>(attachment.parent_owner)]) {
        return {};
      }
      const int parent_label =
          label[static_cast<std::size_t>(attachment.parent_owner)]
               [static_cast<std::size_t>(attachment.chain_position)];
      parent[static_cast<std::size_t>(chain.front())] = parent_label;
    }
    for (int position = 1; position < static_cast<int>(chain.size());
         ++position) {
      parent[static_cast<std::size_t>(
          chain[static_cast<std::size_t>(position)])] =
          chain[static_cast<std::size_t>(position - 1)];
    }
  }
  if (std::any_of(parent.begin(), parent.end(),
                  [](int value) { return value < 0; })) {
    return {};
  }
  return parent;
}

} // namespace

std::vector<int> find_structure(int M) {
  std::vector<int> length(static_cast<std::size_t>(M), 0);
  for (int leaf = 0; leaf < M; ++leaf) {
    while (insert(leaf, 0)) {
      ++length[static_cast<std::size_t>(leaf)];
    }
  }
  const std::vector<int> baseline = collect();
  const int node_count =
      std::accumulate(length.begin(), length.end(), 0);

  bool valid = M >= 1 && node_count >= 2 &&
               baseline.size() == static_cast<std::size_t>(node_count) &&
               length.front() >= 2 &&
               std::all_of(length.begin(), length.end(),
                           [](int value) { return value >= 1; });
  const Parameters parameters = make_parameters(length);
  valid = valid && parameters.nonsingleton_count >= 1 &&
          !parameters.nonsingletons.empty() &&
          parameters.nonsingletons.front() == 0;

  std::vector<Attachment> attachments(static_cast<std::size_t>(M));
  attachments.front().seen = true;
  for (int batch = 0; batch < parameters.batch_count; ++batch) {
    for (int leaf = 0; leaf < M; ++leaf) {
      int successful = 0;
      while (insert(leaf, marker_value(parameters, length, leaf, batch,
                                       successful))) {
        ++successful;
      }
      valid = valid &&
              successful == length[static_cast<std::size_t>(leaf)];
    }
    const std::vector<int> tokens = collect();
    valid = valid &&
            tokens.size() == static_cast<std::size_t>(node_count) &&
            absorb_view(tokens, parameters, length, node_count, batch,
                        attachments);
  }

  if (!valid) {
    return {};
  }
  return build_parent_array(length, attachments, node_count);
}
