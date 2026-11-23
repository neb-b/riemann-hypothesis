module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading

@[expose] public section

-- bundled from Formalism.LocalToGlobal.KernelLattices.JetFieldLeKR
section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H Formalism.MainNotions

section Field

variable {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)

end Field


section KR

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (cD : D.what₂.Tau → ℂ) (D0 : ℕ) (α : TaylorLogMetric.Mono D 1 1)

end KR

section Norm

variable {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
  (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D0 : ℕ)

end Norm

section Tied

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def KerEntTied.VQTie {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (lam : ∀ (_ : D.what₂.Word) (i : ℕ), D.what₂.Tau → DomWeight (D.R.N i))
    (sh : D.what₂.Word → ℕ → D.what₂.Tau → ℤ) : Prop :=
  ∀ u μ i, i ≤ D.R.m → ∀ c : (D.chTw u μ).cls i, Set.range (t.ent.ev u μ i c) =
    {f | ∃ P ∈ DIV.VV D.what₂.LL (lam u i), f = evG ((t.O u μ).frm i) (sh u i) D.what₂.embLL P}

def KerEntTied.WtTie {ex : Extra D L hT Gi Gl K Y cX} (_t : KerEntTied ex) (lam : ∀ (_ : D.what₂.Word) (i : ℕ), D.what₂.Tau → DomWeight (D.R.N i))
    (sh : D.what₂.Word → ℕ → D.what₂.Tau → ℤ) (n : D.what₂.Word → ℕ → D.what₂.Tau → ℕ) : Prop :=
  ∀ u μ i, i < D.R.m → (∀ τ r, (lam u i τ).natW r + n u i τ = nuT D u i τ r) ∧ (∀ τ, sh u i τ + (D.chTw u μ).sSharp i τ = n u i τ) ∧
    (∀ τ, sh u (i + 1) τ = -(D.chTw u μ).sDiv i τ) ∧ JetInVV D.what₂.LL (lam u i) (lam u (i + 1)) (n u i)

end Tied

section Choice

end Choice


open Classical in
def degAt {ι : Type} {a b : ℕ} (m : DVar ι a b →₀ ℕ) (τ : ι) : ℕ := (m.support.filter fun k => k.1 = τ).sum fun k => m k

def Amb.JetsRatDeg {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (dg : X.Tau → ℕ) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), InRange Sall D c N N' x →
    ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, degAt m τ = dg τ) → ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' c x) m

def JetLocal : Prop :=
  ∀ (K : Type) [Field K] [Infinite K] (ι : Type) [Fintype ι] (a b : ℕ) (lam : ι → DomWeight a) (n : ι → ℕ) (J J' : (DVar ι a b →₀ ℕ) → K),
    (∀ m, (∀ τ, degAt m τ = ∑ r, ((lam τ).natW r + n τ)) → J m = J' m) → ∀ P ∈ DIV.VV K lam, jetMap J n P = jetMap J' n P

def KerEntTied.RK {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u μ, Formalism.BasicNotions.DV.Used D μ → ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (m : DVar D.what₂.Tau (D.R.N i) (D.R.N (i + 1)) →₀ ℕ),
    (∀ τ, degAt m τ = ∑ r, nuT D u i τ r) →
    ∃ k : D.what₂.LL, D.what₂.embLL k = ((D.chTw u μ).rhoDet i c * (D.chTw u μ).rhoDet' i c') * jetC (t.O u μ).dgen ((t.O u μ).Th i c c') m

end Formalism.L2.Ker
end
end

-- bundled from Formalism.LocalToGlobal.KernelLattices.KerChTie
section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {X : Fields} {Pr : Primes X} {m : ℕ}

def OffG (Pr : Primes X) (v : HeightOneSpectrum (𝓞 X.E)) : Prop := ∀ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∉ v.asIdeal

def MuValTie (Ch : Chars X Pr m) (G : ChGlob X m) : Prop :=
  ∀ (j : Fin m) (v : HeightOneSpectrum (𝓞 X.E)), OffG Pr v → G.σ₀ ((Ch.muVal j v : X.Kˣ) : X.K) = (((G.mu0 j).val v : ℂˣ) : ℂ)

end Gen

section Mem

variable {D : D7} {u : D.what₂.Word}

def MemLatAt (O : GL3Theta.LiftObj D (D.mem u).C) (π : 𝓞 D.host.E) : Prop :=
  letI := D.host.cmStar
  ∀ i, i ≤ D.R.m → ∃ co : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E),
    (∀ x y, stdH D.host.E (D.R.N i) (co x) (co y) = (D.sp.X i).hT x y) ∧
    (∀ y, co y ∈ (O.L0 i).1 ↔ y ∈ (D.sp.X i).L0) ∧
    ∀ (c : (D.mem u).C.cls i) y, co y ∈ (O.lat i c).1 ↔
      ∃ a ∈ D.clsLat u i c, ∃ b ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c),
        y = a + D.host.conj (π : D.host.E) • b

def IsMemAt (O : GL3Theta.LiftObj D (D.mem u).C) (π : 𝓞 D.host.E) : Prop :=
  O.mt = D.muTil ∧ (∀ i c, O.dt i c = D.detCls u i c) ∧ MemLatAt O π

end Mem

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def KerEntTied.PiSide {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u, t.seam.iE ((t.Pr.piT (t.word u) : 𝓞 t.X.E) : t.X.E) = ((ex.errX.piT u : 𝓞 D.host.E) : D.host.E)

def KerEntTied.memObj {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (u : D.what₂.Word) : GL3Theta.LiftObj D (D.mem u).C :=
  D.memberColumns_twistedChain_base u ▸ t.O u D.what₂.mu0

def KerEntTied.MemSide {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u, (t.memObj u).IsMem → IsMemAt (t.memObj u) (ex.errX.piT u)

structure KerEntTied.ChTie {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop where

  ch_ok : t.Ch.Ok

  muVal : MuValTie t.Ch t.glob

  piT : t.PiSide

  mem : t.MemSide

end Comparison₂

end Formalism.L2.Ker
end
end

