module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.Stable
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.ContinuousCoeffSub
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.Assembly
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.CycAvg
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.SecLine
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.NullTop

@[expose] public section

namespace PositivityTheory.Rg.Sw

open FFTSteps

theorem fft : FFT := assembly stable ext avg pos

theorem cyc_of (h : FFT) : Cyc := fun m n ε c hc P => by
  obtain ⟨Q, hQ, hPQ⟩ := cycAvg m n ε c hc P
  exact ⟨Q, cycFFT h m n ε Q hQ, hPQ⟩

theorem nullIff : NullIff := nullIff_of secLine powSpan

end PositivityTheory.Rg.Sw
