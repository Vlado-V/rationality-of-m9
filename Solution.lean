module

public import M9StacksIntegration.M9PaperResult

namespace M9Rationality

/-- Rationality of the genuine all-family genus-nine coarse moduli space. -/
public theorem main_result :
    M9StandaloneDraft.RationalCoarseSpaceGoal ℂ :=
  M9Native.M9PaperResult.paper_goal

end M9Rationality
