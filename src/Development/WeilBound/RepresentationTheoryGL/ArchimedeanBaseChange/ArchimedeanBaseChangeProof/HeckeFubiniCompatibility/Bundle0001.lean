module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.EntZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.FaceMapCompSuccAboveCastSucc
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0207
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.BridgeSt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH TypeH HeckeM heckeAct Repro)
open PositivityTheory.RgBcC.Bridge (along)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

def CompatEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
  (μb : Measure (G b)) [μb.IsHaarMeasure], ∃ ν : Measure (Hf E a b), ν.IsHaarMeasure ∧ ν.IsMulRightInvariant ∧
    Compat D μa μb ν

def CompatFub : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
  (μb : Measure (G b)) [μb.IsHaarMeasure] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure], Compat D μa μb ν →
  ∀ F : H E a b → ℂ, Continuous F → HasCompactSupport F →
    ∫ g, F g ∂D.μ = ∫ ya : InfinitePlace E → G a, ∫ yb : InfinitePlace E → G b, ∫ h : Hf E a b,
      F (infGL E a (Units.map (Matrix.piRingEquiv (n := Fin a) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
            (MulEquiv.piUnits.symm ya)) * finGL E a h.1,
          infGL E b (Units.map (Matrix.piRingEquiv (n := Fin b) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
            (MulEquiv.piUnits.symm yb)) * finGL E b h.2) ∂ν ∂(Measure.pi fun _ => μb) ∂(Measure.pi fun _ => μa)

def TensTest : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  (μa : Measure (G a)) [μa.IsHaarMeasure] (μb : Measure (G b)) [μb.IsHaarMeasure]
  (Ma : Mods E a) (Mb : Mods E b) (κ : Type) [Fintype κ]
  (ka : Kers Ma) (kb : Kers Mb) va vb (T : ℝ) (ψ : Matrix κ κ (Hf E a b → ℂ)), IsMults μa ka va T → IsMults μb kb vb T →
  IsFinM ψ → IsTestM (tens ka kb ψ) ∧ adjM (tens ka kb ψ) = tens (adjK ka) (adjK kb) (adjF ψ)

def TensMul : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
  (μb : Measure (G b)) [μb.IsHaarMeasure] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure]
  (Ma : Mods E a) (Mb : Mods E b) (κ : Type) [Fintype κ]
  (ka ka' : Kers Ma) (kb kb' : Kers Mb) va va' vb vb' (T T' : ℝ) (ψ ψ' : Matrix κ κ (Hf E a b → ℂ)), Compat D μa μb ν →
  IsMults μa ka va T → IsMults μb kb vb T → IsMults μa ka' va' T' → IsMults μb kb' vb' T' → IsFinM ψ → IsFinM ψ' →
  IsFinM (mulF ν ψ ψ') ∧
    mulM D.μ (tens ka kb ψ) (tens ka' kb' ψ') = tens (convK μa ka ka') (convK μb kb kb') (mulF ν ψ ψ')

def TensTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a) (Mb : Mods E b)
  (κ : Type) [Fintype κ] (ka : Kers Ma) (kb : Kers Mb) (Ta : Ops Ma) (Tb : Ops Mb) (ψ : Matrix κ κ (Hf E a b → ℂ))
  (N : Matrix κ κ ℂ) (g : H E a b), F.trM (tens ka kb ψ) (opM Ta Tb N) g =
    (∏ v, phiOf (Ma v) (Ta v) (ka v) (gInf v g.1)) * (∏ v, phiOf (Mb v) (Tb v) (kb v) (gInf v g.2)) *
      ∑ x, ∑ y, ψ x y (hFin g) * N y x

def VCBridge : Prop := ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) (M : KMod n)
  (Tθ : M.V →L[ℂ] M.V) (k : Mat n → (M.V →L[ℂ] M.V)) val (T : ℝ), (∀ u, Tθ * M.ρ u = M.ρ u * Tθ) → IsMult μ M k val T →
  VCClause (phiOf M Tθ k) → VeryCusp (phiOf M Tθ k)

def Repr {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (D : Dom E a b) {Ma : Mods E a} {Mb : Mods E b}
    {κ : Type} [Fintype κ] (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ))
    (f : Io Ma Mb κ → H E a b → ℂ) : Prop :=
  (∀ i, Continuous (f i)) ∧ ∃ c : ℂ, c ≠ 0 ∧ PositivityTheory.Rg.BcB.E.conv D.μ (tens ka kb ψ) f = c • f

def TypeOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a) (Mb : Mods E b),
  ∃ (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W₁ ∧ FiniteDimensional ℂ W₂ ∧
    ∀ (D : Dom E a b) [MeasurableSpace (G a)] [MeasurableSpace (G b)] (μa : Measure (G a)) (μb : Measure (G b))
      (κ : Type) [Fintype κ] (ka : Kers Ma) (kb : Kers Mb) va vb (T : ℝ) (ψ : Matrix κ κ (Hf E a b → ℂ))
      (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E))) (f : Io Ma Mb κ → H E a b → ℂ),
      IsMults μa ka va T → IsMults μb kb vb T → IsFinM ψ →
      (∀ x y, ∀ u₁ ∈ K₁, ∀ u₂ ∈ K₂, ∀ h, ψ x y ((u₁, u₂) * h) = ψ x y h) → Repr D ka kb ψ f → ∀ i, TypeH K₁ K₂ W₁ W₂ (f i)

def SmoothOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  (μa : Measure (G a)) [μa.IsHaarMeasure] (μb : Measure (G b)) [μb.IsHaarMeasure]
  (Ma : Mods E a) (Mb : Mods E b) (κ : Type) [Fintype κ] (D : Dom E a b)
  (ka : Kers Ma) (kb : Kers Mb) va vb (T : ℝ) (ψ : Matrix κ κ (Hf E a b → ℂ)) (U : Subgroup (Hf E a b))
  (f : Io Ma Mb κ → H E a b → ℂ), IsMults μa ka va T → IsMults μb kb vb T → IsFinM ψ → IsOpen (U : Set (Hf E a b)) →
  (∀ x y, ∀ u ∈ U, ∀ h, ψ x y (u * h) = ψ x y h) → Repr D ka kb ψ f →
  (∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂)) ∧ ∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x)

def GrowthOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι : Type)
  [Fintype ι] (Φ : Matrix ι ι (H E a b → ℂ)) (M : ℕ) (f : ι → H E a b → ℂ) (c : ℂ), IsTestM Φ → (∀ i, Continuous (f i)) →
  LeftInv f → WL2 D M f → c ≠ 0 → PositivityTheory.Rg.BcB.E.conv D.μ Φ f = c • f →
  ∃ C N : ℝ, ∀ i x, ‖f i x‖ ≤ C * Real.exp (N * (logSize x.1 + logSize x.2))

def EigAll {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {ι : Type} (χa : InfinitePlace E → Inf a)
    (χb : InfinitePlace E → Inf b) (f : ι → H E a b → ℂ) : Prop :=
  (∀ i v g m₂, IsEig (χa v) (along v g fun x => f i (x, m₂))) ∧ ∀ i v g m₁, IsEig (χb v) (along v g fun x => f i (m₁, x))

def InfEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Sm E n)) (v : InfinitePlace E)
  (t : Bool → ℕ → ℂ), (∃ φ ∈ S, φ ≠ 0) →
  (∀ φ ∈ S, ∀ g s m, ∀ x ∈ GLs n, gel s m (along v g φ.1) x = t s m • along v g φ.1 x) →
  ∃ χ : Inf n, ∀ s m, GlobalTheory.Dec.gelfVal (χ s) m = t s m

def GelOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
  (μb : Measure (G b)) [μb.IsHaarMeasure] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure]
  (Ma : Mods E a) (Mb : Mods E b) (κ : Type) [Fintype κ]
  (ka : Kers Ma) (kb : Kers Mb) va vb (T : ℝ) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (c c' : ℂ)
  (v : InfinitePlace E) (g : ℝ → ℝ) (s : Bool) (m : ℕ), Compat D μa μb ν → IsMults μa ka va T → IsMults μb kb vb T →
  IsFinM ψ → IsBump g T →
  ((∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂)) ∧ ∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x)) →
  (∀ i, Continuous (f i)) → c ≠ 0 → PositivityTheory.Rg.BcB.E.conv D.μ (tens ka kb ψ) f = c • f →
  (∀ k', IsKer μa (Ma v) [] g (ka v) → IsKer μa (Ma v) [(s, m)] g k' →
    PositivityTheory.Rg.BcB.E.conv D.μ (tens (Function.update ka v k') kb ψ) f = c' • f →
    ∀ i y m₂, ∀ x ∈ GLs a, gel s m (along v y fun z => f i (z, m₂)) x = (c' / c) • along v y (fun z => f i (z, m₂)) x) ∧
  ∀ k', IsKer μb (Mb v) [] g (kb v) → IsKer μb (Mb v) [(s, m)] g k' →
    PositivityTheory.Rg.BcB.E.conv D.μ (tens ka (Function.update kb v k') ψ) f = c' • f →
    ∀ i y m₁, ∀ x ∈ GLs b, gel s m (along v y fun z => f i (m₁, z)) x = (c' / c) • along v y (fun z => f i (m₁, z)) x

def ActVal : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
  (μb : Measure (G b)) [μb.IsHaarMeasure] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure]
  (Ma : Mods E a) (Mb : Mods E b) (κ : Type) [Fintype κ]
  (ka ka' : Kers Ma) (kb kb' : Kers Mb) va va' vb vb' (T T' : ℝ) (ψ ψ' : Matrix κ κ (Hf E a b → ℂ))
  (f : Io Ma Mb κ → H E a b → ℂ) χa χb, Compat D μa μb ν → IsMults μa ka va T → IsMults μb kb vb T → IsFinM ψ →
  Repr D ka kb ψ f →
  ((∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂)) ∧ ∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x)) →
  EigAll χa χb f → IsMults μa ka' va' T' → IsMults μb kb' vb' T' → IsFinM ψ' →
  PositivityTheory.Rg.BcB.E.conv D.μ (tens ka' kb' ψ') f = (valA va' χa * valA vb' χb) • convF ν ψ' f

def FinHecke : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure] (A κ : Type)
  [Fintype A] [Fintype κ] (ψ : Matrix κ κ (Hf E a b → ℂ)) (U : Subgroup (Hf E a b)), IsFinM ψ →
  IsOpen (U : Set (Hf E a b)) → IsCompact (U : Set (Hf E a b)) → (∀ x y, ∀ u ∈ U, ∀ h, ψ x y (h * u) = ψ x y h) →
  ∃ h : HeckeM E a b (A × κ), (∀ i j, i.1 ≠ j.1 → h i j = 0) ∧ (∀ p q x y, h (p, x) (p, y) = h (q, x) (q, y)) ∧
    ∀ f : A × κ → H E a b → ℂ, (∀ i, ∀ u ∈ U, ∀ x, f i (x * finH u) = f i x) → convF ν ψ f = heckeAct h f

def AutOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) (f : ι → H E a b → ℂ)
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E))) (W₁ : Submodule ℂ (Kinf E a → ℂ))
  (W₂ : Submodule ℂ (Kinf E b → ℂ)) χa χb (C N : ℝ), IsOpen (K₁ : Set (GL (Fin a) (Af E))) →
  IsOpen (K₂ : Set (GL (Fin b) (Af E))) → FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ → LeftInv f →
  (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) → (∀ i x, ‖f i x‖ ≤ C * Real.exp (N * (logSize x.1 + logSize x.2))) → EigAll χa χb f →
  (∀ φ ∈ slices₁ f, IsAutForm φ) ∧ (∀ φ ∈ slices₂ f, IsAutForm φ) ∧
    (∀ τ, HasInfCharGL (Submodule.span ℂ (slices₁ f)) τ (mOf χa τ)) ∧
    ∀ τ, HasInfCharGL (Submodule.span ℂ (slices₂ f)) τ (mOf χb τ)

def InfConv : Prop := ∀ (n : ℕ) (x : ℕ → Fin n → ℂ) (y : Fin n → ℂ),
  (∀ m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (x k) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal y m))) → ∀ ε : ℝ, 0 < ε →
  ∀ᶠ k in atTop, Multiset.Rel (fun p q => ‖p - q‖ ≤ ε) (Multiset.map (x k) Finset.univ.val) (Multiset.map y Finset.univ.val)

def ReproEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)]
  [BorelSpace (GA E N)] (ν : Measure (GA E N)) [ν.IsHaarMeasure] (K : Subgroup (GL (Fin N) (Af E)))
  (W : Submodule ℂ (Kinf E N → ℂ)) (R : ℝ), IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → Repro ν K W R

end PositivityTheory.Rg.BcB.CG

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.MultHasCompactSupport
section
noncomputable section

open MeasureTheory Matrix
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PositivityTheory.Rg.BcB.CG

variable {n : ℕ}

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem isUnit_det_unitary (u : Matrix.unitaryGroup (Fin n) ℂ) : IsUnit (u.1.det) :=
  Matrix.isUnit_det_of_left_inverse (Unitary.star_mul_self_of_mem u.2)

theorem mul_mem_GLs {y : Mat n} (hy : y ∈ GLs n) (u₁ u₂ : Matrix.unitaryGroup (Fin n) ℂ) :
    u₁.1 * y * u₂.1 ∈ GLs n := by
  show (u₁.1 * y * u₂.1).det ≠ 0
  rw [Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero (isUnit_det_unitary u₁).ne_zero hy) (isUnit_det_unitary u₂).ne_zero

section Mult

variable [MeasurableSpace (G n)] {μ : Measure (G n)} {M : KMod n} {k : Mat n → (M.V →L[ℂ] M.V)}
  {val : Inf n → ℂ} {T : ℝ}

theorem mult_continuous (h : IsMult μ M k val T) : Continuous fun y : G n => k y.val := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  have e : (fun y : G n => k y.val) = fun y => ∑ i, c i • ks i y.val :=
    funext fun y => hk _ (val_mem_GLs y)
  rw [e]
  exact continuous_finsetSum _ fun i _ =>
    ((hks i).2.1.continuousOn.comp_continuous Units.continuous_val val_mem_GLs).const_smul (c i)

theorem mult_exists_lg (h : IsMult μ M k val T) : ∃ R : ℝ, ∀ y ∈ GLs n, R < lg y → k y = 0 := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  choose R hR using fun i => (hks i).2.2.1
  refine ⟨∑ i, |R i|, fun y hy hlt => ?_⟩
  rw [hk _ hy]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hR i y hy (lt_of_le_of_lt ((le_abs_self _).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (R j)) (Finset.mem_univ i))) hlt), smul_zero]

theorem mult_hasCompactSupport (h : IsMult μ M k val T) : HasCompactSupport fun y : G n => k y.val := by
  obtain ⟨R, hR⟩ := mult_exists_lg h
  exact HasCompactSupport.intro ((GlobalTheory.T.length_continuous_proper_sublevel n).2 R) fun y hy => hR _ (val_mem_GLs y) (not_le.1 hy)

theorem mult_equivariant (h : IsMult μ M k val T) : ∀ y ∈ GLs n, ∀ u₁ u₂ : Matrix.unitaryGroup (Fin n) ℂ,
    k (u₁.1 * y * u₂.1) = M.ρ u₁ * k y * M.ρ u₂ := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  intro y hy u₁ u₂
  rw [hk _ (mul_mem_GLs hy u₁ u₂), hk _ hy, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hks i).2.2.2.1 y hy u₁ u₂]
  simp only [mul_smul_comm, smul_mul_assoc]

theorem mult_equivariant_val (h : IsMult μ M k val T) (y : G n) (u₁ u₂ : Matrix.unitaryGroup (Fin n) ℂ) :
    k (u₁.1 * y.val * u₂.1) = M.ρ u₁ * k y.val * M.ρ u₂ :=
  mult_equivariant h _ (val_mem_GLs y) u₁ u₂

end Mult

section Ent

variable {M : KMod n}

theorem continuous_ent {X : Type} [TopologicalSpace X] {f : X → (M.V →L[ℂ] M.V)} (hf : Continuous f) (i j : Ix M) :
    Continuous fun x => ent M (f x) i j :=
  continuous_const.inner (hf.clm_apply continuous_const)

theorem hasCompactSupport_ent {X : Type} [TopologicalSpace X] {f : X → (M.V →L[ℂ] M.V)} (hf : HasCompactSupport f)
    (i j : Ix M) : HasCompactSupport fun x => ent M (f x) i j :=
  hf.comp_left (g := fun A => ent M A i j) (ent_zero M i j)

variable [MeasurableSpace (G n)] {μ : Measure (G n)} {k : Mat n → (M.V →L[ℂ] M.V)} {val : Inf n → ℂ} {T : ℝ}

theorem mult_ent (h : IsMult μ M k val T) (i j : Ix M) :
    Continuous (fun y : G n => ent M (k y.val) i j) ∧ HasCompactSupport (fun y : G n => ent M (k y.val) i j) :=
  ⟨continuous_ent (mult_continuous h) i j, hasCompactSupport_ent (mult_hasCompactSupport h) i j⟩

end Ent

end PositivityTheory.Rg.BcB.CG

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PReproCa
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.RgBcC

namespace PositivityTheory.Rg.BcB.CG.ReproL

theorem norm_cosh_sub_one_le {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖Complex.cosh z - 1‖ ≤ 2 * ‖z‖ := by
  have h1 := Complex.norm_exp_sub_one_le hz
  have h2 := Complex.norm_exp_sub_one_le (x := -z) (by rwa [norm_neg])
  rw [norm_neg] at h2
  have e : Complex.cosh z - 1 = ((Complex.exp z - 1) + (Complex.exp (-z) - 1)) / 2 := by
    rw [show Complex.cosh z = (Complex.exp z + Complex.exp (-z)) / 2 from rfl]; ring
  rw [e, norm_div]
  have h3 := norm_add_le (Complex.exp z - 1) (Complex.exp (-z) - 1)
  have h4 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h4]
  linarith

theorem continuous_cas (N : ℕ) : Continuous fun χ : Inf N => cas χ := by
  have hA : ∀ f : Inf N → Fin N → ℂ, Continuous f → Continuous fun χ => Formalism.REAL.Amat (f χ) := by
    intro f hf
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Formalism.REAL.Amat, Matrix.of_apply]
    split_ifs
    · exact (continuous_apply a).comp hf
    · exact continuous_const
    · exact continuous_const
  have hg : ∀ s : Bool, Continuous fun χ : Inf N => GlobalTheory.Dec.gelfVal (χ s) 2 := by
    intro s
    unfold GlobalTheory.Dec.gelfVal
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
    have hf : Continuous fun χ : Inf N => fun c : Fin N => χ s c + ((N : ℂ) - 1) / 2 :=
      continuous_pi fun c => (continuous_apply_apply s c).add continuous_const
    exact ((hA _ hf).pow 2).matrix_elem a b
  unfold cas
  exact continuous_const.mul ((hg true).add (hg false))

theorem exists_bump (N : ℕ) (R : ℝ) : ∃ (g : ℝ → ℝ) (T : ℝ), 0 < T ∧ IsBump g T ∧
    ∀ χ : Inf N, (∀ s i, ‖χ s i‖ ≤ R) → 1 / 2 ≤ ‖coshT g (cas χ)‖ := by
  have hS : IsCompact {χ : Inf N | ∀ s i, ‖χ s i‖ ≤ R} := by
    have e : {χ : Inf N | ∀ s i, ‖χ s i‖ ≤ R} =
        Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) R := by
      ext χ; simp [Set.mem_pi]
    rw [e]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (continuous_cas N).continuousOn
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set s := Real.sqrt C' with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set T : ℝ := 1 / (4 * (s + 1)) with hT
  have hT0 : 0 < T := by positivity
  have hTs : T * s ≤ 1 / 4 := by
    rw [hT, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  let f : ContDiffBump (0 : ℝ) := ⟨T / 2, T, by positivity, by linarith⟩
  set g : ℝ → ℝ := f.normed volume with hg
  have hsupp : ∀ t, g t ≠ 0 → |t| < T := by
    intro t ht
    have : t ∈ Function.support g := ht
    rw [hg, ContDiffBump.support_normed_eq] at this
    simpa [Metric.mem_ball, Real.dist_eq] using this
  refine ⟨g, T, hT0, ⟨ContDiffBump.contDiff_normed f, fun t => ?_, fun t ht => ?_⟩, ?_⟩
  · have := ContDiffBump.normed_neg f (μ := volume) t
    simpa [hg] using this
  · by_contra h
    exact absurd (hsupp t h) (not_lt.2 ht.le)
  intro χ hχ
  set c := cas χ with hc
  have hcC : ‖c‖ ≤ C' := (hC χ hχ).trans (le_max_left _ _)
  have hroot : ‖c ^ (1 / 2 : ℂ)‖ ≤ s := by
    have e : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_cpow_real, ← Real.sqrt_eq_rpow, hs]
    exact Real.sqrt_le_sqrt hcC
  have hgc : Continuous g := (ContDiffBump.contDiff_normed f (n := 0)).continuous
  have hgcs : HasCompactSupport g := ContDiffBump.hasCompactSupport_normed f
  have hgC : HasCompactSupport fun t => (g t : ℂ) := hgcs.comp_left Complex.ofReal_zero
  have hcont1 : Continuous fun t : ℝ => Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) :=
    Complex.continuous_cosh.comp (Complex.continuous_ofReal.mul continuous_const)
  have hi1 : Integrable fun t : ℝ => (g t : ℂ) * Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) :=
    ((Complex.continuous_ofReal.comp hgc).mul hcont1).integrable_of_hasCompactSupport (hgC.mul_right)
  have hi2 : Integrable fun t : ℝ => (g t : ℂ) :=
    (Complex.continuous_ofReal.comp hgc).integrable_of_hasCompactSupport hgC
  have hone : ∫ t, (g t : ℂ) = 1 := by
    rw [integral_complex_ofReal, hg, ContDiffBump.integral_normed]; simp
  have h3 : ∫ t, (g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1) =
      (∫ t, (g t : ℂ) * Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ))) - ∫ t, (g t : ℂ) := by
    rw [← integral_sub hi1 hi2]; congr 1; funext t; ring
  have hdiff : coshT g c - 1 = ∫ t, (g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1) := by
    rw [h3, hone]; rfl
  have hbound : ∀ t, ‖(g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1)‖ ≤ g t * (1 / 2) := by
    intro t
    by_cases h0 : g t = 0
    · simp [h0]
    have ht := hsupp t h0
    have hz : ‖(t : ℂ) * c ^ (1 / 2 : ℂ)‖ ≤ 1 / 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |t| * ‖c ^ (1 / 2 : ℂ)‖ ≤ T * s := mul_le_mul ht.le hroot (norm_nonneg _) hT0.le
        _ ≤ 1 / 4 := hTs
    have hgt : 0 ≤ g t := ContDiffBump.nonneg_normed f t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgt]
    refine mul_le_mul_of_nonneg_left ?_ hgt
    calc ‖Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1‖ ≤ 2 * ‖(t : ℂ) * c ^ (1 / 2 : ℂ)‖ :=
          norm_cosh_sub_one_le (hz.trans (by norm_num))
      _ ≤ 1 / 2 := by linarith
  have hle : ‖coshT g c - 1‖ ≤ 1 / 2 := by
    rw [hdiff]
    calc ‖∫ t, (g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1)‖ ≤ ∫ t, g t * (1 / 2) :=
          norm_integral_le_of_norm_le ((hgc.mul continuous_const).integrable_of_hasCompactSupport hgcs.mul_right)
            (Filter.Eventually.of_forall hbound)
      _ = 1 / 2 := by rw [integral_mul_const, hg, ContDiffBump.integral_normed]; ring
  have := norm_sub_norm_le (1 : ℂ) (1 - coshT g c)
  rw [sub_sub_cancel, norm_one, norm_sub_rev] at this
  linarith

theorem exists_enum {N : ℕ} (m : Multiset ℂ) (h : Multiset.card m = N) :
    ∃ e : Fin N → ℂ, Multiset.map e Finset.univ.val = m := by
  subst h
  refine ⟨fun i => m.toList.get (Fin.cast (by simp) i), ?_⟩
  rw [Fin.univ_val_map]
  have e : List.ofFn (fun i : Fin (Multiset.card m) => m.toList.get (Fin.cast (by simp) i)) = m.toList :=
    List.ext_get (by simp) (by simp)
  rw [e, Multiset.coe_toList]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem exists_chi (hB : Bridge.BridgeSt) (R : ℝ) (v : InfinitePlace E) (φ : Sm E N)
    (hR : PositivityTheory.Rg.BcB.SpectralAccumulation.InfBdd R (Submodule.span ℂ {φ})) :
    ∃ χ : Inf N, (∀ s i, ‖χ s i‖ ≤ R) ∧ ∀ g : GA E N, IsEig χ (Bridge.along v g φ.1) := by
  obtain ⟨m1, h1, b1⟩ := hR v.embedding
  obtain ⟨m2, h2, b2⟩ := hR (ComplexEmbedding.conjugate v.embedding)
  obtain ⟨e1, he1⟩ := exists_enum m1 h1.1
  obtain ⟨e2, he2⟩ := exists_enum m2 h2.1
  refine ⟨fun s => if s then e1 else e2, ?_, ?_⟩
  · intro s i
    cases s
    · exact b2 _ (he2 ▸ Multiset.mem_map_of_mem e2 (Finset.mem_univ_val i))
    · exact b1 _ (he1 ▸ Multiset.mem_map_of_mem e1 (Finset.mem_univ_val i))
  · intro g
    have key := (hB E N (Submodule.span ℂ {φ}) v (fun s => if s then e1 else e2)).2
      ⟨by simpa [he1] using h1, by simpa [he2] using h2⟩
    exact key φ (Submodule.mem_span_singleton_self φ) g

end PositivityTheory.Rg.BcB.CG.ReproL
end
end

