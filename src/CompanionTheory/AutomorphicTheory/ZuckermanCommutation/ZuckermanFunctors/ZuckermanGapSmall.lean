module

public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanIngredients
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.Bundle0001
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.Bridge

@[expose] public section

namespace CompanionTheory.Zuck

theorem zuckerman_gap_small : ZuckSm thr := zuckSm_of zuckerman_ingredients zuckerman_library_bounds

theorem zuckerman_gap : BranchingSupport.ZuckG := zuckG_of_sm (fun _ hn ε => thr_le hn ε) zuckerman_gap_small

end CompanionTheory.Zuck
