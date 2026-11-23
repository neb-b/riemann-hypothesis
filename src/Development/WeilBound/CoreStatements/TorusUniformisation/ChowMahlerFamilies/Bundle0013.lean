module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0019
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FirstLatticeBaseChange
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0028
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0009
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0003
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0012
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0010

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.AdaptedEigenbasisExists
section
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.AdaptedEigenbasis

variable {E : Type} [Field E] [NumberField E] {K W : Type} [Field K] [AddCommGroup W] [Module K W]

theorem exists_dual {q : ℕ} {w : Fin q → W} (hw : LinearIndependent K w) :
    ∃ f : Fin q → Module.Dual K W, ∀ j j', f j (w j') = if j = j' then 1 else 0 := by
  obtain ⟨g, hg⟩ := (Fintype.linearCombination K w).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot'.2 fun c hc => funext (Fintype.linearIndependent_iff.1 hw c hc))
  refine ⟨fun j => LinearMap.proj j ∘ₗ g, fun j j' => ?_⟩
  have h := LinearMap.congr_fun hg (Pi.single j' 1)
  simp only [LinearMap.comp_apply, Fintype.linearCombination_apply_single, one_smul, LinearMap.id_apply] at h
  simp [h, Pi.single_apply]

theorem form_eigProj {ρ : 𝓞 E →+* Module.End K W} {τ : E →+* K} {φ : Module.Dual K W}
    (h : ∀ (b : 𝓞 E) x, φ (ρ b x) = τ (b : E) * φ x) (x : W) : φ (HT.eigProj ρ τ x) = φ x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h, smul_eq_mul,
    ← mul_assoc]
  rw [← Finset.sum_mul]
  have : ∑ k, τ (HT.dualInt E k) * τ ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_one τ, ← HT.LatBasic.sum_dualInt_mul, map_sum]
    simp
  rw [this, one_mul]

theorem eigProj_fst {ρ : 𝓞 E →+* Module.End K W} {ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)}
    (h : ∀ a y, (ρH a y).1 = ρ a y.1) (σ : E →+* K) (y : W × Module.Dual K W) :
    (HT.eigProj ρH σ y).1 = HT.eigProj ρ σ y.1 := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Prod.fst_sum, Prod.smul_fst, h]


omit [NumberField E] in
theorem inr_mem_iff {ρ : 𝓞 E →+* Module.End K W} {ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)}
    {bar : 𝓞 E ≃+* 𝓞 E} {σ σ' : E →+* K} (h : ∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a)))
    (hσ : ∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) (hb : ∀ a, bar (bar a) = a) (φ : Module.Dual K W) :
    ((0, φ) : W × Module.Dual K W) ∈ HT.eigSp ρH σ ↔ ∀ (b : 𝓞 E) x, φ (ρ b x) = σ' (b : E) * φ x := by
  simp only [HT.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
  constructor
  · intro H b x
    have h1 := H (bar b)
    rw [h, hb] at h1
    rw [hσ]
    exact LinearMap.congr_fun (congrArg Prod.snd h1) x
  · intro H a
    rw [h]
    refine Prod.ext (by simp) (LinearMap.ext fun x => ?_)
    have h1 := H (bar a) x
    rw [hσ, hb] at h1
    exact h1

end PositivityTheory.Xgn.AdaptedEigenbasis

open PositivityTheory.Xgn.AdaptedEigenbasis in
theorem PositivityTheory.Xgn.adapted_eigenbasis_exists : ∀ (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [CharZero K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : 𝓞 E →+* Module.End K W) (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* K) (p q : ℕ) (v : Fin p → W) (w : Fin q → W), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → LinearIndependent K v → Submodule.span K (Set.range v) = HT.eigSp ρ σ → LinearIndependent K w → Submodule.span K (Set.range w) = HT.eigSp ρ σ' → ∃ u, IsAdapted ρH σ v w u ∧ LinearIndependent K u ∧ Submodule.span K (Set.range u) = HT.eigSp ρH σ := by
  intro E _ _ K W _ _ _ _ _ ρ ρH bar σ σ' p q v w h1 h2 hσ hb hv hvs hw hws
  obtain ⟨f, hf⟩ := exists_dual hw
  have hvm : ∀ i, v i ∈ HT.eigSp ρ σ := fun i => hvs ▸ Submodule.subset_span ⟨i, rfl⟩
  have hwm : ∀ j, w j ∈ HT.eigSp ρ σ' := fun j => hws ▸ Submodule.subset_span ⟨j, rfl⟩
  set φ : Fin q → Module.Dual K W := fun j => f j ∘ₗ HT.eigProj ρ σ' with hφ
  have hφw : ∀ j j', φ j (w j') = if j = j' then 1 else 0 := fun j j' => by
    simp only [hφ, LinearMap.comp_apply, HT.LatBasic.eigProj_of_mem (hwm j'), hf]
  have hφe : ∀ j (b : 𝓞 E) x, φ j (ρ b x) = σ' (b : E) * φ j x := fun j b x => by
    simp only [hφ, LinearMap.comp_apply, HodgeDeterminantLattice.eigProj_act, map_smul, smul_eq_mul]
  set l : Fin p → W × Module.Dual K W := fun i => HT.eigProj ρH σ (v i, 0) with hl
  have hl1 : ∀ i, (l i).1 = v i := fun i => by
    simp only [hl, eigProj_fst h1, HT.LatBasic.eigProj_of_mem (hvm i)]
  have hlm : ∀ i, l i ∈ HT.eigSp ρH σ := fun i => HT.LatBasic.eigProj_mem _ _ _
  have hum : ∀ i, Fin.addCases (motive := fun _ => W × Module.Dual K W) l (fun j => (0, φ j)) i ∈
      HT.eigSp ρH σ := fun i => by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using hlm i
    · simpa only [Fin.addCases_right] using (inr_mem_iff h2 hσ hb _).2 (hφe j)
  refine ⟨Fin.addCases (motive := fun _ => W × Module.Dual K W) l (fun j => (0, φ j)),
    ⟨hum, fun i => by simp only [Fin.addCases_left, hl1],
      fun j => by simp only [Fin.addCases_right, hφw, implies_true, and_self]⟩, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fin.sum_univ_add] at hc
    simp only [Fin.addCases_left, Fin.addCases_right] at hc
    have hc1 : ∀ i, c (Fin.castAdd q i) = 0 := by
      refine Fintype.linearIndependent_iff.1 hv _ ?_
      have := congrArg Prod.fst hc
      simpa [Prod.fst_sum, hl1] using this
    intro i
    refine Fin.addCases hc1 (fun j => ?_) i
    have := LinearMap.congr_fun (congrArg Prod.snd hc) (w j)
    simpa [Prod.snd_sum, hc1, hφw] using this
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hum i
    · intro y hy
      have hy1 : y.1 ∈ Submodule.span K (Set.range v) := by
        rw [hvs, HT.LatBasic.mem_eigSp]
        intro a
        rw [← h1, HT.LatBasic.mem_eigSp.1 hy a, Prod.smul_fst]
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hy1
      set z := y - ∑ i, c i • l i with hz
      have hzm : z ∈ HT.eigSp ρH σ :=
        sub_mem hy (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hlm i))
      have hz1 : z = (0, z.2) := Prod.ext (by simp [hz, Prod.fst_sum, hl1, hc]) rfl
      rw [hz1, inr_mem_iff h2 hσ hb] at hzm
      have hz2 : z.2 = ∑ j, z.2 (w j) • φ j := by
        refine LinearMap.ext fun x => ?_
        have hx : HT.eigProj ρ σ' x ∈ Submodule.span K (Set.range w) := hws ▸ HT.LatBasic.eigProj_mem _ _ _
        obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
        have hd' : ∀ j, φ j x = d j := fun j => by
          rw [← form_eigProj (hφe j) x, ← hd]
          simp [hφw]
        rw [← form_eigProj hzm x, ← hd]
        simp [hd', mul_comm]
      have e : y = ∑ i, c i • l i + ∑ j, z.2 (w j) • ((0, φ j) : W × Module.Dual K W) := by
        rw [← sub_eq_iff_eq_add', ← hz]
        refine Prod.ext ?_ ?_
        · rw [hz1]
          simp [Prod.fst_sum]
        · rw [Prod.snd_sum]
          exact hz2
      rw [e]
      refine add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨Fin.castAdd q i, by simp only [Fin.addCases_left]⟩)) (Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.natAdd p j, by simp only [Fin.addCases_right]⟩))
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFamPull
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_fam_pull
open ReciprocityTheory.ChartRestriction.G.Geo (div_mem_chartRing)
open PositivityTheory.Xgn.A_pull_line (comb)
open PositivityTheory.Xgn.A_pull_exists (pow_mul_mem)
open GlobalTheory.CompanionTheory.Ar.Num.LocFreeBC (smul_mem_spanOver mem_spanOver_of_mem)

theorem latFamily_join {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {K : Type} [Fintype K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) {K' : Type} [Fintype K'] {ι' : K' → Type}
    [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) {V : Type} [AddCommGroup V] [Module Ω V]
    (L : (∀ k, ι k) → AddSubgroup V) (hfam : IsLatFamily O x L) (f : V → V) (hf : ∀ v, f v = v) :
    IsLatFamily O (joinCoord x z) (fun s =>
      spanOver (chartRing O (mseg (joinCoord x z)) s) (f '' (L (restrictChart s) : Set V))) := by
  have hj : ∀ s : ∀ k : K ⊕ K', Sum.elim ι ι' k, mseg (joinCoord x z) s =
      mseg x (restrictChart s) * mseg z (fun k => s (.inr k)) :=
    fun s => PositivityTheory.Xgn.A_pull_line.mseg_join (AlgHom.id O Ω) x z s
  have hne : ∀ s : ∀ k : K ⊕ K', Sum.elim ι ι' k, mseg (joinCoord x z) s ≠ 0 →
      mseg x (restrictChart s) ≠ 0 := by
    intro s hs
    rw [hj] at hs
    exact left_ne_zero_of_mul hs
  refine ⟨fun s _ a ha v hv => smul_mem_spanOver _ _ ha hv, ?_⟩
  intro s t hs ht v hv
  beta_reduce at hv ⊢
  have hq := div_mem_chartRing (o := O) (mseg (joinCoord x z)) t s
  set q := mseg (joinCoord x z) s / mseg (joinCoord x z) t with hqdef
  rw [spanOver] at hv
  induction hv using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩ := hy
    obtain ⟨n, hn⟩ := pow_mul_mem (joinCoord x z) s t hs a ha
    obtain ⟨m, hm⟩ := hfam.2 _ _ (hne s hs) (hne t ht) e he
    have hw := div_mem_chartRing (o := O) (mseg (joinCoord x z)) t (comb (restrictChart t) s)
    set w := mseg (joinCoord x z) (comb (restrictChart t) s) / mseg (joinCoord x z) t with hwdef
    have ht' := hne t ht
    have hqw : q = w * (mseg x (restrictChart s) / mseg x (restrictChart t)) := by
      have h1 : mseg (joinCoord x z) (comb (restrictChart t) s) =
          mseg x (restrictChart t) * mseg z (fun k => s (.inr k)) := hj _
      rw [hqdef, hwdef, h1, hj s]
      field_simp
    refine ⟨n + m, ?_⟩
    have h : q ^ (n + m) • a • f e = (q ^ n * a * w ^ m) •
        f ((mseg x (restrictChart s) / mseg x (restrictChart t)) ^ m • e) := by
      rw [hf, hf, smul_smul, smul_smul, pow_add, mul_assoc (q ^ n * a), ← mul_pow, ← hqw]
      congr 1
      ring
    rw [h]
    exact smul_mem_spanOver _ _ (mul_mem hn (pow_mem hw m)) (mem_spanOver_of_mem _ ⟨_, hm, rfl⟩)
  | zero => exact ⟨0, by rw [smul_zero]; exact zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    have h : q ^ (m + n) • (a + b) = q ^ n • q ^ m • a + q ^ m • q ^ n • b := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm n m]
    rw [h]
    exact add_mem (smul_mem_spanOver _ _ (pow_mem hq n) hm) (smul_mem_spanOver _ _ (pow_mem hq m) hn)
  | neg a _ ha =>
    obtain ⟨m, hm⟩ := ha
    exact ⟨m, by rw [smul_neg]; exact neg_mem hm⟩

theorem charData {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω]
    (hinj : Function.Injective (algebraMap O Ω)) {F : Type} [Zero F] [One F] {Sg : Type} (p : ℕ)
    (hp : p.Prime) (w : O) (χ : Sg → F → O)
    (h : (p : O) ≠ 0 ∧ (∃ u : O, IsUnit u ∧ w ^ (p - 1) = u * (p : O)) ∧ ¬ IsUnit (p : O) ∧ (0 : F) ≠ 1 ∧
      ∀ τ, χ τ 0 = 0 ∧ χ τ 1 = 1) (R : Subalgebra O Ω) :
    CharData R p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) := by
  obtain ⟨h0, ⟨u, hu, hw⟩, -, h01, hχ⟩ := h
  obtain ⟨u, rfl⟩ := hu
  refine ⟨?_, R.algebraMap_mem _, ⟨algebraMap O Ω ((u⁻¹ : Oˣ) * w ^ (p - 2)), R.algebraMap_mem _, ?_⟩, h01,
    fun τ => ⟨?_, ?_, fun a => R.algebraMap_mem _⟩⟩
  · rw [← map_natCast (algebraMap O Ω)]
    exact (map_ne_zero_iff _ hinj).2 h0
  · have h2 : p - 1 = p - 2 + 1 := by have := hp.two_le; omega
    rw [← map_mul, mul_assoc, ← pow_succ, ← h2, hw, Units.inv_mul_cancel_left, map_natCast]
  · simp only [(hχ τ).1, map_zero]
  · simp only [(hχ τ).2, map_one]

theorem mul_std_le {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {n : ℕ} (R R' : Subalgebra O Ω)
    (w : Ω) (A : AddSubgroup (Fin n → Ω)) (h : mulLat w (stdLat R _) ≤ A) :
    mulLat w (stdLat R' _) ≤ spanOver R' (bcMap Ω Ω _ '' (A : Set (Fin n → Ω))) := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' : ∀ i, y i ∈ R' := fun i => hy i (Set.mem_univ i)
  have e : (DistribSMul.toAddMonoidHom (Fin n → Ω) w) y =
      ∑ i, y i • (w • (Pi.single i (1 : Ω) : Fin n → Ω)) := by
    change w • y = _
    conv_lhs => rw [pi_eq_sum_univ' y]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  rw [e]
  refine sum_mem fun i _ => smul_mem_spanOver _ _ (hy' i) (mem_spanOver_of_mem _ ⟨_, h ⟨Pi.single i 1, ?_, rfl⟩, rfl⟩)
  intro j _
  change (Pi.single i (1 : Ω) : Fin n → Ω) j ∈ R
  rw [Pi.single_apply]
  split_ifs
  exacts [one_mem _, zero_mem _]

theorem span_eq {O Ω V : Type} [CommRing O] [Field Ω] [Algebra O Ω] [AddCommGroup V] [Module Ω V]
    (R : Subalgebra O Ω) (L L' : AddSubgroup V) (h : L = L') (f : V → V) (hf : ∀ v, f v = v) :
    AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e} = spanOver R (f '' (L' : Set V)) := by
  obtain rfl : f = id := funext hf
  rw [h, Set.image_id]
  rfl

end PositivityTheory.Xgn.A_fam_pull

theorem PositivityTheory.Xgn.t_fam_pull : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), IsLatticeFamily O (joinCoord x z) p w χ φ (pullFamily O x z D) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₁ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))) ∧ ((∀ c, mseg x c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg x) c) _) ≤ (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg (joinCoord x z)) c) _) ≤ (pullFamily O x z D c).af (chartRing O (mseg (joinCoord x z)) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₂ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))))) ∧ ((∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O (joinCoord x z) u a fun c => (pullFamily O x z D c).xId (fun a => algebraMap O Ω (χ τ a)) i))) ∧ ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → ∃ (Lie' W' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (r τ) (Fin (r τ) → Ω)) (Om' OmHT' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (s τ) (Fin (s τ) → Ω)), HasBundles O (joinCoord x z) (pullFamily O x z D) Lie' W' Om' OmHT' ∧ ∀ τ, IsPull O x z (Lie τ) (Lie' τ) ∧ IsPull O x z (W τ) (W' τ) ∧ IsPull O x z (Om τ) (Om' τ) ∧ IsPull O x z (OmHT τ) (OmHT' τ) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x hinj F _ _ _ n Sg _ r s p hp w χ φ D hD K' _ _ ι' _ z
  have hc := ((PositivityTheory.Xgn.t_chart_noeth_frac O Ω K ι x).2.2 K' ι' z).2
  have hcd := PositivityTheory.Xgn.A_fam_pull.charData hinj p hp w χ hD.char
  refine ⟨⟨?_, fun τ => ?_, hD.char, fun c h => ?_, fun c h => ?_⟩, fun h1 => ⟨fun c h => ?_, fun haf =>
    ⟨fun c h τ => ?_, fun h2 c h => ?_⟩, fun hl τ i => ?_⟩, fun Lie W Om OmHT hB => ?_⟩
  · exact PositivityTheory.Xgn.A_fam_pull.latFamily_join x z _ hD.famM _ (fun _ => rfl)
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hD.fam τ
    exact ⟨PositivityTheory.Xgn.A_fam_pull.latFamily_join x z _ a1 _ (fun _ => rfl),
      PositivityTheory.Xgn.A_fam_pull.latFamily_join x z _ a2 _ (fun _ => rfl),
      PositivityTheory.Xgn.A_fam_pull.latFamily_join x z _ a3 _ (fun _ => rfl),
      PositivityTheory.Xgn.A_fam_pull.latFamily_join x z _ a4 _ (fun _ => rfl),
      PositivityTheory.Xgn.A_fam_pull.latFamily_join x z _ a5 _ (fun _ => rfl),
      PositivityTheory.Xgn.A_fam_pull.latFamily_join x z _ a6 _ (fun _ => rfl),
      PositivityTheory.Xgn.A_fam_pull.latFamily_join x z _ a7 _ (fun _ => rfl)⟩
  · exact (_root_.GlobalTheory.CompanionTheory.Ar.Num.lattice_base_change_larger_ring (D (restrictChart c)) _ p _ _ (hcd _) (hD.base _ (hc c h).1) Ω _
      (fun a ha => (hc c h).2 ha)).2
  · exact PositivityTheory.Xgn.test_facts_base_change (D (restrictChart c)) _ _ (hc c h).2 p _ _ φ (hD.test _ (hc c h).1)
  · exact ((PositivityTheory.Xgn.good_lattice_base_change (D (restrictChart c)) _ p _ _ (hcd _) (hD.base _ (hc c h).1)
      (h1 _ (hc c h).1)).2 Ω _ (fun a ha => (hc c h).2 ha)).1
  · have e := ((((PositivityTheory.Xgn.good_lattice_base_change (D (restrictChart c)) _ p _ _ (hcd _) (hD.base _ (hc c h).1)
      (h1 _ (hc c h).1)).2 Ω _ (fun a ha => (hc c h).2 ha)).2 τ).1)
    exact (PositivityTheory.Xgn.A_fam_pull.mul_std_le _ _ _ _ (haf _ (hc c h).1 τ)).trans e.ge
  · exact ((_root_.GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.main (D (restrictChart c)) _ p _ _ (hcd _) (hD.base _ (hc c h).1)
      (h1 _ (hc c h).1) (h2 _ (hc c h).1) (haf _ (hc c h).1)).2 Ω _ (fun a ha => (hc c h).2 ha)).1
  · obtain ⟨u, a, hu, hA⟩ := hl τ i
    refine ⟨u, pullDeg (K' := K') a, hu, fun c h v => ?_⟩
    refine PositivityTheory.Xgn.A_pull_line.main (AlgHom.id O Ω) x z u a _ hA
      (fun c => (pullFamily O x z D c).xId (fun a => algebraMap O Ω (χ τ a)) i) (fun c h => ?_) c h v
    have e := ((((PositivityTheory.Xgn.good_lattice_base_change (D (restrictChart c)) _ p _ _ (hcd _) (hD.base _ (hc c h).1)
      (h1 _ (hc c h).1)).2 Ω _ (fun a ha => (hc c h).2 ha)).2 τ).2.2 i)
    exact e.trans (PositivityTheory.Xgn.A_fam_pull.span_eq _ _ _ rfl _ (fun _ => rfl)).symm
  · choose Lie' hLie using fun τ => (PositivityTheory.Xgn.t_pull_exists O Ω K ι x _ _ (Lie τ)).1 K' ι' z
    choose W' hW using fun τ => (PositivityTheory.Xgn.t_pull_exists O Ω K ι x _ _ (W τ)).1 K' ι' z
    choose Om' hOm using fun τ => (PositivityTheory.Xgn.t_pull_exists O Ω K ι x _ _ (Om τ)).1 K' ι' z
    choose OmHT' hOmHT using fun τ => (PositivityTheory.Xgn.t_pull_exists O Ω K ι x _ _ (OmHT τ)).1 K' ι' z
    refine ⟨Lie', W', Om', OmHT', fun τ c h => ?_, fun τ => ⟨hLie τ, hW τ, hOm τ, hOmHT τ⟩⟩
    obtain ⟨b1, b2, b3, b4⟩ := hB τ _ (hc c h).1
    exact ⟨(hLie τ c h).trans (PositivityTheory.Xgn.A_fam_pull.span_eq _ _ _ b1 _ (fun _ => rfl)),
      (hW τ c h).trans (PositivityTheory.Xgn.A_fam_pull.span_eq _ _ _ b2 _ (fun _ => rfl)),
      (hOm τ c h).trans (PositivityTheory.Xgn.A_fam_pull.span_eq _ _ _ b3 _ (fun _ => rfl)),
      (hOmHT τ c h).trans (PositivityTheory.Xgn.A_fam_pull.span_eq _ _ _ b4 _ (fun _ => rfl))⟩
end

