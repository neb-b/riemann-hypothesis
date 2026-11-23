module

public import Formalism.IncomingBounds.FlowDegreeBounds.MaxFlowValueAttained
public import Formalism.IncomingBounds.FlowDegreeBounds.Bundle0001
public import Formalism.IncomingBounds.FlowDegreeBounds.LemmaFd
public import Mathlib
public import Formalism.IncomingBounds.Bundle0001
public import Formalism.IncomingBounds.FlowDegreeBounds.Bundle0002
public import Formalism.IncomingBounds.FlowDegreeBounds.Cayley

@[expose] public section

namespace Formalism.IncomingBounds

theorem lemmaFa : LemmaFa := strongDuality
theorem lemmaFc : LemmaFc := lemmaFc_of maxFlowValueAttained strongDuality
theorem incomingBound : IncomingBound := incomingBound_of maxFlowValueAttained strongDuality
theorem cayleyId : CayleyId := cayleyIdentity

end Formalism.IncomingBounds
