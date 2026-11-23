module

public import Mathlib
public import Formalism.HermitianCurvature.StatementTB
public import Formalism.HermitianCurvature.Bundle0001
public import Formalism.HermitianCurvature.Bundle0003

@[expose] public section

-- bundled from Formalism.HermitianCurvature.LatticeHerglotzBound
section
namespace Formalism.FourierDecayAlt.crystallineComparison

open MeasureTheory Filter Topology Finset

noncomputable section

open Classical

abbrev V (f : ℕ) := Fin f → ℂ

def mfac (K : ℕ) (L a : ℝ) : ℝ := if a = 0 then 1 else min 1 ((L / a) ^ K)

def mL {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (σ : V f) : ℝ := ∏ v, mfac K (L v) ‖σ v‖

def pat {f : ℕ} (L : Fin f → ℝ) (σ : V f) : Finset (Fin f) := univ.filter (fun v => L v < ‖σ v‖)

def psi {f : ℕ} (z : V f) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ v, (z v + starRingEnd ℂ (z v)))

def dualSet {f : ℕ} (La : Submodule ℤ (V f)) : Set (V f) := {σ | ∀ z ∈ La, psi (σ * z) = 1}

def fourier {f : ℕ} (g : V f → ℝ) (σ : V f) : ℂ := ∫ z, (g z : ℂ) * psi (σ * z)

def PDOn {f : ℕ} (T : Set (V f)) (A : V f → ℂ) : Prop :=
  ∀ (S : Finset (V f)) (c : V f → ℂ), (∀ σ ∈ S, σ ∈ T) →
    0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, A (σ - σ') * c σ * starRingEnd ℂ (c σ')).re

def Bdd {α : Type} (g : α → ℂ) : Prop := ∃ B : ℝ, ∀ x, ‖g x‖ ≤ B

def IsMean {Λ : Type} [AddCommGroup Λ] (LIM : (Λ → ℂ) → ℂ) : Prop :=
  (∀ g h, Bdd g → Bdd h → LIM (g + h) = LIM g + LIM h) ∧
  (∀ (c : ℂ) g, Bdd g → LIM (c • g) = c * LIM g) ∧
  (∀ g, Bdd g → (∀ x, 0 ≤ (g x).re ∧ (g x).im = 0) → 0 ≤ (LIM g).re ∧ (LIM g).im = 0) ∧
  LIM (fun _ => 1) = 1 ∧
  (∀ g (σ : Λ), Bdd g → LIM (fun x => g (x + σ)) = LIM g)

def atInfAll (f : ℕ) : Filter (V f) :=
  ⨅ v : Fin f, Filter.comap (fun x : V f => ‖x v‖) Filter.atTop

def IsMeanInf {f : ℕ} (Λ : AddSubgroup (V f)) (LIM : (Λ → ℂ) → ℂ) : Prop :=
  IsMean LIM ∧ ∀ g : Λ → ℂ, Bdd g →
    Tendsto g (Filter.comap (fun x : Λ => (x : V f)) (atInfAll f)) (𝓝 0) → LIM g = 0

def MajIntegral : Prop :=
  ∀ (K : ℕ) (x : ℝ), 2 < K → 0 < x →
    Integrable (fun l : ℂ => mfac K x ‖l‖) ∧
      ∫ l : ℂ, mfac K x ‖l‖ = Real.pi * x ^ 2 * K / ((K : ℝ) - 2)

def MajIntegralProd : Prop :=
  ∀ (f K : ℕ) (x : Fin f → ℝ), 2 < K → (∀ v, 0 < x v) →
    Integrable (fun l : V f => mL K x l) ∧
      ∫ l : V f, mL K x l = ∏ v, (Real.pi * x v ^ 2 * K / ((K : ℝ) - 2))

def MeanBound : Prop :=
  ∀ (Λ : Type) [AddCommGroup Λ] (LIM : (Λ → ℂ) → ℂ) (g : Λ → ℂ) (B : ℝ),
    IsMean LIM → (∀ x, ‖g x‖ ≤ B) → ‖LIM g‖ ≤ B

def MeanExists : Prop :=
  ∀ (f : ℕ) (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La],
    ∃ LIM : (La.toAddSubgroup → ℂ) → ℂ, IsMeanInf La.toAddSubgroup LIM

def MeanSplit : Prop :=
  ∀ (f : ℕ) (Λ : AddSubgroup (V f)) (LIM : (Λ → ℂ) → ℂ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (a r : V f → H) (Nh : V f → ℂ) (B : ℝ),
    IsMeanInf Λ LIM → (∀ x, ‖a x‖ ≤ B ∧ ‖r x‖ ≤ B) →
    (∀ σ ∈ Λ, Tendsto (fun x => inner ℂ (a x) (a (x + σ))) (atInfAll f) (𝓝 (Nh σ))) →
    (∀ σ ∈ Λ, Tendsto (fun x => inner ℂ (a x) (r (x + σ))) (atInfAll f) (𝓝 0)) →
    (∀ σ ∈ Λ, Tendsto (fun x => inner ℂ (r x) (a (x + σ))) (atInfAll f) (𝓝 0)) →
    (∀ σ ∈ Λ, LIM (fun x : Λ => inner ℂ (a x + r x) (a ((x : V f) + σ) + r ((x : V f) + σ))) =
        Nh σ + LIM (fun x : Λ => inner ℂ (r x) (r ((x : V f) + σ)))) ∧
    PDOn (Λ : Set (V f)) (fun σ => LIM (fun x : Λ => inner ℂ (r x) (r ((x : V f) + σ))))

def LatticeHerglotzBound : Prop :=
  ∀ (f : ℕ) (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La]
    (N : V f → ℝ) (A : V f → ℂ),
    (∀ z, 0 ≤ N z) → LowerSemicontinuous N → Integrable N → PDOn (dualSet La) A →
    Summable (fun σ : dualSet La => ‖fourier N σ + A σ‖) →
    ∀ (z₀ : V f) (S : Finset (V f)), (∀ z ∈ S, z - z₀ ∈ La) →
      ZLattice.covolume La * ∑ z ∈ S, N z ≤ ∑' σ : dualSet La, ‖fourier N σ + A (σ : V f)‖

def SumForm {E W : Type} [Field E] (D : TB.Data E W) (ε : ℝ) (i s : ℕ) (w : W) (Mv : ℝ) : Prop :=
  ∃ θ : W → ℝ, TB.IsProb (D.Wb (D.cnt w + s * D.K)) θ ∧
    ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - s) → ∀ κ, TB.PSDOn Y κ →
      ∀ (t₀ : E) (S : Finset E), (∀ t ∈ S, t ≠ 0 ∧ t - t₀ ∈ D.La (i - s + 1) s) →
        ∑ t ∈ S, (D.Nst ε i s w Y κ t t).re ≤
          Mv * ∑ w' ∈ D.Wb (D.cnt w + s * D.K), θ w' * D.N0 ε (i - s) w' Y κ

def EstBlockOfSumForm : Prop :=
  ∀ (E W : Type) [Field E] (D : TB.Data E W) (C₄ : ℝ), D.GramPSD → D.WordsPos →
    (∀ ε, 0 < ε → ∀ i s, 2 ≤ s → s ≤ i → i ≤ D.r + 1 → ∀ w ∈ D.Wall,
      D.cnt w + (s + 1) * D.K ≤ D.Ntop → D.vol (i - s + 1) s ≤ 1 →
      ∃ Mv, Mv ≤ C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') ∧ SumForm D ε i s w Mv) →
    D.EstBlock C₄

end

end Formalism.FourierDecayAlt.crystallineComparison
end

-- bundled from Formalism.HermitianCurvature.PrimeToDifferent
section
namespace Formalism.FourierDecayAlt.S6

open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors

section Defs

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

abbrev FI := FractionalIdeal (𝓞 E)⁰ E

noncomputable def deg : ℕ := finrank ℚ (maximalRealSubfield E)

noncomputable def dd : FI E := ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FI E)

def Unram : Prop :=
  differentIdeal ℤ (𝓞 E) =
    (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))

def UnramAbove (g : ℕ) : Prop :=
  IsCoprime (differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E)) (Ideal.span {(g : 𝓞 E)})

def PrimeToDifferent (g : ℕ) : Prop :=
  IsCoprime (differentIdeal ℤ (𝓞 E)) (Ideal.span {(g : 𝓞 E)})

noncomputable def rd : ℝ := ((|discr E| : ℤ) : ℝ) ^ ((finrank ℚ E : ℝ)⁻¹)

noncomputable def idl (g : ℕ) (k ν : ℤ) : FI E :=
  dd E ^ ν * FractionalIdeal.spanSingleton _ ((g : E) ^ k)

def zsub (A : FI E) : Submodule ℤ E := (A : Submodule (𝓞 E) E).restrictScalars ℤ

noncomputable def conjZ : E →ₗ[ℤ] E :=
  (complexConj E).toAlgHom.toRingHom.toAddMonoidHom.toIntLinearMap

def ConjStable (A : FI E) : Prop := ∀ x ∈ A, complexConj E x ∈ A

noncomputable def twLat (A B : FI E) (s : ℕ) : Submodule ℤ E :=
  zsub E A ⊓ (zsub E B).comap (LinearMap.id - ((-1 : ℤ) ^ s) • conjZ E)

noncomputable def perLat (g : ℕ) (ν : ℤ) (s : ℕ) : Submodule ℤ E :=
  twLat E (idl E g 1 ν) (idl E g 2 ν) s

noncomputable def liftLat (g : ℕ) (ν : ℤ) (s : ℕ) : Submodule ℤ E :=
  twLat E (idl E g (-1) (-ν)) (idl E g 0 (-ν)) s

noncomputable def dualIdl (g : ℕ) (ν : ℤ) : FI E := idl E g (-1) (-(ν + 1))

noncomputable def liftIdl (g : ℕ) (ν : ℤ) : FI E := idl E g (-1) (-ν)

def dualLat (g : ℕ) (L : Submodule ℤ E) : Submodule ℤ E where
  carrier := {x | ∀ y ∈ L, Algebra.trace ℚ E (x * y / g) ∈ (algebraMap ℤ ℚ).range}
  zero_mem' := fun y _ => by simp
  add_mem' := fun {a b} ha hb y hy => by
    have h : (a + b) * y / g = a * y / g + b * y / g := by ring
    rw [h, map_add (f := _)]
    exact add_mem (ha y hy) (hb y hy)
  smul_mem' := fun n a ha y hy => by
    have h : (n • a) * y / g = n • (a * y / g) := by
      simp only [zsmul_eq_mul]; ring
    rw [h, map_zsmul]
    exact zsmul_mem (ha y hy) n

noncomputable def idx (L M : Submodule ℤ E) : ℕ := L.toAddSubgroup.relIndex M.toAddSubgroup

noncomputable def frameLat (L : Submodule ℤ E) (c : ℝ) :
    Submodule ℤ (mixedEmbedding.mixedSpace E) :=
  (L.map (mixedEmbedding E).toAddMonoidHom.toIntLinearMap).map
    ((c • (LinearMap.id : mixedEmbedding.mixedSpace E →ₗ[ℝ] mixedEmbedding.mixedSpace E)).restrictScalars ℤ)

def locAt (P : Ideal (𝓞 (maximalRealSubfield E))) (L : Submodule ℤ E) : Set E :=
  {t | ∃ a : 𝓞 (maximalRealSubfield E), a ∉ P ∧ algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L}

def nuBlock (r i s : ℤ) : ℤ := 2 * r + 3 - 2 * i - s

end Defs

section Small

def DegreeFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    finrank ℚ E = 2 * deg E ∧ Fintype.card (InfinitePlace E) = deg E ∧ 0 < deg E

def PowConjStable : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (k ν : ℤ),
    ConjStable E (idl E g k ν)

def UnramRelative : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unram E →
    differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ ∧ ∀ g : ℕ, UnramAbove E g

def Between : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A B : FI E) (s : ℕ),
    B ≤ A → ConjStable E B → zsub E B ≤ twLat E A B s ∧ twLat E A B s ≤ zsub E A

def IndexCore : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : FI E) (g s : ℕ),
    A ≠ 0 → ConjStable E A → 0 < g → UnramAbove E g →
    idx E (twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s) (zsub E A) = g ^ deg E ∧
    idx E (zsub E (A * FractionalIdeal.spanSingleton _ (g : E)))
      (twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s) = g ^ deg E

def DualSubset : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g →
    dualLat E g (perLat E g ν s) ≤ twLat E (dualIdl E g ν) (idl E g 0 (-(ν + 1))) (s + 1)

def DualSupset : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unram E →
    ∀ (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g →
      twLat E (dualIdl E g ν) (idl E g 0 (-(ν + 1))) (s + 1) ≤ dualLat E g (perLat E g ν s)

def NormIdl : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (k ν : ℤ), 0 < g →
    √(FractionalIdeal.absNorm (idl E g k ν) : ℝ) = ((g : ℝ) ^ k * rd E ^ ν) ^ deg E


open scoped Classical in
def CovolumeIndex : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : FI E) (L : Submodule ℤ E) (c : ℝ),
    B ≠ 0 → c ≠ 0 → zsub E B ≤ L → idx E (zsub E B) L ≠ 0 →
    DiscreteTopology (frameLat E L c) ∧
    Submodule.span ℝ (frameLat E L c : Set (mixedEmbedding.mixedSpace E)) = ⊤ ∧
    ZLattice.covolume (E := mixedEmbedding.mixedSpace E) (frameLat E L c) =
      |c| ^ (2 * deg E) * (FractionalIdeal.absNorm B : ℝ) * (2⁻¹ : ℝ) ^ deg E *
        √((|discr E| : ℤ) : ℝ) / (idx E (zsub E B) L : ℝ)

def IdealsMatch : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (r i s : ℤ),
    dualIdl E g (nuBlock r i s) = liftIdl E g (nuBlock r i (s - 1)) ∧
    dualIdl E g (nuBlock r i s) = idl E g (-1) (-(2 * r + 4 - 2 * i - s)) ∧
    nuBlock r i s = 2 * (r + 1) - i - (i - 1 + s)

def LocTw : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A B : FI E) (s : ℕ)
    (P : Ideal (𝓞 (maximalRealSubfield E))), P.IsPrime → ∀ t : E,
    (t ∈ locAt E P (twLat E A B s) ↔
      t ∈ locAt E P (zsub E A) ∧ t - (-1) ^ s * complexConj E t ∈ locAt E P (zsub E B))

def LocOrdinary : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (k ν : ℤ)
    (P : Ideal (𝓞 (maximalRealSubfield E))), P.IsPrime → (g : 𝓞 (maximalRealSubfield E)) ∉ P →
    locAt E P (zsub E (idl E g k ν)) = locAt E P (zsub E (idl E g 0 ν))

def IsFLattice (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule ℤ E) : Prop :=
  (∀ (a : 𝓞 (maximalRealSubfield E)) (t : E), t ∈ L →
    algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L) ∧
  ∀ t : E, ∃ n : ℕ, 0 < n ∧ (n : E) * t ∈ L

def TwIsFLattice : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A B : FI E) (s : ℕ),
    B ≠ 0 → B ≤ A → ConjStable E B → IsFLattice E (twLat E A B s)

end Small

section Text


open scoped Classical in
def LatticeFacts (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ) (s : ℕ) :
    Prop :=
  zsub E (idl E g 2 ν) ≤ perLat E g ν s ∧
  perLat E g ν s ≤ zsub E (idl E g 1 ν) ∧
  idx E (perLat E g ν s) (zsub E (idl E g 1 ν)) = g ^ deg E ∧
  idx E (zsub E (idl E g 2 ν)) (perLat E g ν s) = g ^ deg E ∧
  dualLat E g (perLat E g ν s) ≤ zsub E (dualIdl E g ν) ∧
  idx E (dualLat E g (perLat E g ν s)) (zsub E (dualIdl E g ν)) = g ^ deg E ∧
  liftLat E g ν s ≤ zsub E (liftIdl E g ν) ∧
  idx E (liftLat E g ν s) (zsub E (liftIdl E g ν)) = g ^ deg E ∧
  √(FractionalIdeal.absNorm (dualIdl E g ν) : ℝ) = ((g : ℝ) * rd E ^ (ν + 1)) ^ (-(deg E : ℤ)) ∧
  DiscreteTopology (frameLat E (perLat E g ν s) (rd E ^ (-ν))) ∧
  Submodule.span ℝ
    (frameLat E (perLat E g ν s) (rd E ^ (-ν)) : Set (mixedEmbedding.mixedSpace E)) = ⊤ ∧
  ZLattice.covolume (E := mixedEmbedding.mixedSpace E) (frameLat E (perLat E g ν s) (rd E ^ (-ν))) =
    (rd E / 2) ^ deg E * (g : ℝ) ^ (3 * deg E)

def LatticesGeneral : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unram E →
    ∀ (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g → LatticeFacts E g ν s

def AssembleLattices : Prop :=
  DegreeFacts → PowConjStable → UnramRelative → Between → IndexCore →
    DualSubset → DualSupset → NormIdl → CovolumeIndex → LatticesGeneral

def TypedModel : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g →
    PrimeToDifferent E g →
    ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsPrime → (g : 𝓞 (maximalRealSubfield E)) ∈ P →
    ∀ (K : Type) [Field K] (o : Subring K) (σ : E →+* K),
      (∀ x : E, x ∈ locAt E P (zsub E 1) ↔ σ x ∈ o ∧ σ (complexConj E x) ∈ o) →
      ∀ t : E, (t ∈ locAt E P (perLat E g ν s) ↔
        (σ t / (g : K), (-1) ^ s * σ (complexConj E t) / (g : K)) ∈ Formalism.FourierDecayAlt.I.orderR o (g : K))

end Text

end Formalism.FourierDecayAlt.S6
end

