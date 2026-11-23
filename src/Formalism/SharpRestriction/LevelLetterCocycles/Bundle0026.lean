module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0023
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsPosConstLagrangeCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.ThmELiftAtOf
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingEveryOrdering
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0014
public import Formalism.SharpRestriction.LevelLetterCocycles.BoundedNumeratorPowerSummability
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ExportFamilies
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.Divisibility.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ExtDataExtTool
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.LiftingTheory Formalism.MainNotions.CrystallineLiftingInputs

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem extData_win (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) (i : ZMod n) (hηb : η ≤ b i) :
    Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η i ⊆
      Set.Icc (-(Formalism.MainNotions.RamifiedCoefficientChains.MiW d b S η i : ℤ)) (Formalism.MainNotions.RamifiedCoefficientChains.hiW d b S η i : ℤ) := by
  intro x hx
  unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at hx
  unfold Formalism.MainNotions.RamifiedCoefficientChains.MiW Formalism.MainNotions.RamifiedCoefficientChains.hiW
  split_ifs at hx ⊢ with h <;> simp only [Set.mem_union, Set.mem_Icc] at hx ⊢ <;> push_cast at hx ⊢ <;> omega

theorem extData_lin {FF M I : Type} [AddCommGroup FF] [Module O FF] [AddCommGroup M] [Module O M] [Fintype I]
    (P : M → Prop) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (c : O) x, P x → P (c • x))
    (bF : Module.Basis I O FF) (Φ : FF →ₗ[O] M) (h : ∀ j, P (Φ (bF j))) (f : FF) : P (Φ f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← bF.sum_equivFun f, map_sum]
  exact Finset.sum_induction _ P hadd h0 fun j _ => by rw [map_smul]; exact hsmul _ _ (h j)

theorem extData_extTool [NeZero n] (W : LocWach PD LL O v n)
    (hH : Formalism.MainNotions.ElementDenominator.coreHerrExtΔ W) (hExt : Formalism.MainNotions.LiftingTheory.liftb_HExt W) (hOne : Formalism.MainNotions.LiftingTheory.liftb_HOne W)
    (hKer : Formalism.MainNotions.LiftingTheory.liftb_HKer W) (hJmp : Formalism.MainNotions.CrystallineLiftingBounds.coreJumps PD LL O)
    (hEx : ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
      IsSESLat (Qp := Qp) (O := O) ι π → Function.Injective (W.map ι) ∧ Function.Surjective (W.map π) ∧
        ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x)
    (hdex : W.DelF.card = PD.p - 1 → ∃ d : O, d * (W.DelF.card : O) = 1)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h6 : Formalism.MainNotions.DeltaInvariantLattices.WachSaturationExactness W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hQ : Formalism.MainNotions.CrystallineLiftingInputs.QTool W) :
    ExtTool W := by
  intro d T₁ T₂ F b S η m hS FF _ _ _ _ g
  have hS' := hS
  obtain ⟨hA, h11, -, hOd, hζ, hSur, hJ1, -, hab, -⟩ := hS
  have hηb : ∀ i, η ≤ b i := fun i => by
    have h0 := Formalism.MainNotions.RamifiedCoefficientChains.aR_nonneg PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) (by omega)
    have h1 := hab i
    have h2 : (η : ℝ) ≤ (b i : ℝ) := by linarith
    exact_mod_cast h2
  set Mi := Formalism.MainNotions.RamifiedCoefficientChains.MiW d b S η with hMi
  set hi := Formalism.MainNotions.RamifiedCoefficientChains.hiW d b S η with hhi
  set a := ⌈Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η)⌉₊ with ha
  have c1 : IsCrys PD T₁.ρ := hSur.1
  have c2 : IsCrys PD T₂.ρ := hSur.2.1
  have hOc : IsCrys PD W.one.ρ := hOne.1
  have hJL1 : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi := fun i τ hτ x hx => extData_win d b S η i (hηb i) (hJ1 i τ hτ x hx)
  obtain ⟨T₀, ι₀, hses₀, c0⟩ := hKer T₁ T₂ F hSur
  have hJY : ∀ (Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L),
      IsSESLat (Qp := Qp) (O := O) ι π → IsCrys PD Y.ρ → Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W Y Mi hi := by
    intro Y ι π hses hY τ i hτ x hx
    rcases (hJmp T₂ Y W.one ι π hses c2 hY hOc τ x).1 hx with h | h
    · exact hJL1 i τ hτ x ((hJmp T₀ T₁ T₂ ι₀ F hses₀ c0 c1 c2 τ x).2 (Or.inr h))
    · rw [hOne.2.1 τ x h]
      simp
  have hQ1 := (hQ d T₁ T₂ F b S η m Mi hi hS' hJL1).2
  set N := eWA PD.p (Hmax n Mi hi) with hN
  have hK : ∀ (Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L),
      IsSESLat (Qp := Qp) (O := O) ι π → IsCrys PD Y.ρ → ∀ i : ZMod n,
        Kills W π i (lp W N) ∧ Kills W π i (qp W ^ a) := fun Y ι π hses hY i =>
    ⟨(hQ1 Y ι π hses hY i).2.1, (hQ1 Y ι π hses hY i).2.2⟩

  let I := Module.Free.ChooseBasisIndex O FF
  let bF : Module.Basis I O FF := Module.Free.chooseBasis O FF
  have one := fun j : I => extDataOne_exists W hH hExt hOne hEx hdex h5 h6 h9 hA hζ hOd T₂ c2 Mi hi a N
    hJY hK (g (bF j) : G → T₂.V) (g (bF j)).2
  choose yj zj μj νj hZj hcZj hclj hRelj using one
  let y : FF →ₗ[O] W.DD T₂ := bF.constr O yj
  let z : FF →ₗ[O] W.DD T₂ := bF.constr O zj
  let μ : ZMod n → FF →ₗ[O] W.DD T₂ := fun i => bF.constr O fun j => μj j i
  let ν : ZMod n → FF →ₗ[O] W.DD T₂ := fun i => bF.constr O fun j => νj j i
  have hyb : ∀ j, y (bF j) = yj j := fun j => bF.constr_basis O yj j
  have hzb : ∀ j, z (bF j) = zj j := fun j => bF.constr_basis O zj j
  have hμb : ∀ i j, μ i (bF j) = μj j i := fun i j => bF.constr_basis O (fun j => μj j i) j
  have hνb : ∀ i j, ν i (bF j) = νj j i := fun i j => bF.constr_basis O (fun j => νj j i) j
  refine ⟨N, y, z, μ, ν, fun f => ?_, fun i f => ?_⟩
  · have hκ : ((g f : ↥(latticeFiniteCocycles PD T₂.L)) : G → T₂.V) ∈ latticeCocycles T₂.L := (Submodule.mem_inf.1 (g f).2).1
    have hyf : y f = ∑ j, bF.equivFun f j • yj j := by simp [y, Module.Basis.constr_apply_fintype]
    have hzf : z f = ∑ j, bF.equivFun f j • zj j := by simp [z, Module.Basis.constr_apply_fintype]
    have hpair : ((y f, z f) : W.DD T₂ × W.DD T₂) = ∑ j, bF.equivFun f j • ((yj j, zj j) : W.DD T₂ × W.DD T₂) := by
      rw [hyf, hzf]
      ext <;> simp [Prod.fst_sum, Prod.snd_sum]
    have hmem : ((y f, z f) : W.DD T₂ × W.DD T₂) ∈ herrZ1Δ (W.γD T₂ W.gamK) (W.φD T₂) W.DelF (W.γD T₂) := by
      rw [hpair]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hZj j)
    refine ⟨⟨(y f, z f), hmem⟩, hκ, rfl, ?_⟩
    have hx : (⟨(y f, z f), hmem⟩ : ↥(herrZ1Δ (W.γD T₂ W.gamK) (W.φD T₂) W.DelF (W.γD T₂))) =
        ∑ j, bF.equivFun f j • (⟨(yj j, zj j), hZj j⟩ :
          ↥(herrZ1Δ (W.γD T₂ W.gamK) (W.φD T₂) W.DelF (W.γD T₂))) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      exact hpair
    have hsum : (⟨((g f : ↥(latticeFiniteCocycles PD T₂.L)) : G → T₂.V), hκ⟩ : ↥(latticeCocycles T₂.L)) =
        ∑ j, bF.equivFun f j • (⟨((g (bF j) : ↥(latticeFiniteCocycles PD T₂.L)) : G → T₂.V), hcZj j⟩ : ↥(latticeCocycles T₂.L)) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      conv_lhs => rw [← bF.sum_equivFun f]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Submodule.coe_sum]
      simp only [map_smul, Submodule.coe_smul]
    show W.clK T₂ (⟨(y f, z f), hmem⟩ : ↥(herrZ1Δ (W.γD T₂ W.gamK) (W.φD T₂) W.DelF (W.γD T₂))) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum, hsum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, hclj, ← Submodule.mkQ_apply, map_sum]
  · let sA : LetA O n → (W.DD T₂ →ₗ[O] W.DD T₂) := fun c =>
      ((c • LinearMap.id : W.DD T₂ →ₗ[LetA O n] W.DD T₂)).restrictScalars O
    have hsA : ∀ c x, sA c x = c • x := fun c x => by
      simp only [sA, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have hNs : ∀ (c : O) (x : W.DD T₂), x ∈ W.N T₂ → c • x ∈ W.N T₂ := fun c x h => by
      rw [← algebraMap_smul (LetA O n) c x]; exact (W.N T₂).smul_mem _ h
    have hJs : ∀ (c : O) (x : W.DD T₂), x ∈ pullJ W T₂ (i - 1) 1 → c • x ∈ pullJ W T₂ (i - 1) 1 :=
      fun c x h => by rw [← algebraMap_smul (LetA O n) c x]; exact Submodule.smul_mem _ _ h
    let Φ4 : FF →ₗ[O] W.DD T₂ := ((PD.p : ℕ) : O) ^ N • (sA (letE i) ∘ₗ y) + (W.φD T₂ ∘ₗ μ (i - 1)) - μ i
    have hΦ4 : ∀ f', Φ4 f' = ((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y f') + W.φD T₂ (μ (i - 1) f') -
        μ i f' := fun f' => by
      simp only [Φ4, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, hsA]
    have hΦ4b : ∀ j, Φ4 (bF j) = ((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • yj j) +
        W.φD T₂ (μj j (i - 1)) - μj j i := fun j => by rw [hΦ4, hyb, hμb, hμb]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact extData_lin (DL W T₂ i) ⟨smul_zero _, fun δ _ => map_zero _⟩
        (fun x y hx hy => Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_add W T₂ hx hy) (fun c x hx => Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T₂ c hx)
        bF (μ i) (fun j => by rw [hμb]; exact (hRelj j i).1) f
    · exact extData_lin (DL W T₂ i) ⟨smul_zero _, fun δ _ => map_zero _⟩
        (fun x y hx hy => Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_add W T₂ hx hy) (fun c x hx => Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T₂ c hx)
        bF (ν i) (fun j => by rw [hνb]; exact (hRelj j i).2.1) f
    · let Φ3 : FF →ₗ[O] W.DD T₂ := ((PD.p : ℕ) : O) ^ N • (sA (letE i) ∘ₗ z) + ((W.γ T₂) ∘ₗ μ i - μ i)
      have hΦ3 : ∀ f', Φ3 f' = ((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • z f') +
          (W.γ T₂ (μ i f') - μ i f') := fun f' => by
        simp only [Φ3, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, hsA]
      rw [← hΦ3]
      exact extData_lin (InPN W T₂ 1) ⟨0, (W.N T₂).zero_mem, fun δ _ => map_zero _, (smul_zero _).symm⟩
        (fun x y hx hy => Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_add W T₂ hx hy) (fun c x hx => Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_smul W T₂ c hx)
        bF Φ3 (fun j => by rw [hΦ3, hzb, hμb]; exact (hRelj j i).2.2.1) f
    · have := extData_lin (fun x => x ∈ W.N T₂) (W.N T₂).zero_mem (fun x y hx hy => (W.N T₂).add_mem hx hy)
        hNs bF (sA (qp W ^ Mi i) ∘ₗ Φ4) (fun j => by
          rw [LinearMap.comp_apply, hsA, hΦ4b]; exact (hRelj j i).2.2.2.1) f
      rwa [LinearMap.comp_apply, hsA, hΦ4] at this
    · have := extData_lin (fun x => ∃ s : ℕ, ((PD.p : ℕ) : O) ^ s • x ∈ pullJ W T₂ (i - 1) 1)
        ⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩
        (fun x y ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ => ⟨s₁ + s₂, by
          simp only [smul_add, pow_add, mul_smul]
          rw [smul_comm (((PD.p : ℕ) : O) ^ s₁) (((PD.p : ℕ) : O) ^ s₂) x]
          exact Submodule.add_mem _ (hJs _ _ h₁) (hJs _ _ h₂)⟩)
        (fun c x ⟨s₀, h₀⟩ => ⟨s₀, by rw [smul_comm]; exact hJs c _ h₀⟩)
        bF (sA (qp W ^ hi i) ∘ₗ Φ4) (fun j => by
          rw [LinearMap.comp_apply, hsA, hΦ4b]; exact (hRelj j i).2.2.2.2.1) f
      rwa [LinearMap.comp_apply, hsA, hΦ4] at this
    · let Φ6 : FF →ₗ[O] W.DD T₂ := ((PD.p : ℕ) : O) ^ N • ν i - sA (qp W ^ a) ∘ₗ μ i
      have hΦ6 : ∀ f', Φ6 f' = ((PD.p : ℕ) : O) ^ N • ν i f' - qp W ^ a • μ i f' := fun f' => by
        simp only [Φ6, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, hsA]
      rw [← hΦ6]
      exact extData_lin (fun x => x ∈ W.N T₂) (W.N T₂).zero_mem (fun x y hx hy => (W.N T₂).add_mem hx hy)
        hNs bF Φ6 (fun j => by rw [hΦ6, hνb, hμb]; exact (hRelj j i).2.2.2.2.2) f

end Formalism.MainNotions.RamifiedCoefficientChains.Sh

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfUnramifiedLifting
section
noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem finiteDimensional_max_unramified (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(K0 K) := by
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have h : K0 K ≤ K.1 := inf_le_left
  exact FiniteDimensional.of_injective (IntermediateField.inclusion h).toLinearMap
    (IntermediateField.inclusion h).injective

theorem fd_Ks (K : FinExt l) (s : ℕ) : FiniteDimensional ℚ_[l] ↥(Ks K s) := by
  classical
  have hpos : 0 < l ^ s := pow_pos (Fact.out : l.Prime).pos _
  have hfin : Set.Finite {x : Om l | x ^ (l ^ s) = 1} :=
    (Polynomial.nthRoots (l ^ s) (1 : Om l)).toFinset.finite_toSet.subset fun x hx => by
      simpa [Polynomial.mem_nthRoots hpos] using hx
  haveI : Finite {x : Om l | x ^ (l ^ s) = 1} := hfin.to_subtype
  haveI : FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ s) = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x hx =>
      IsIntegral.of_pow hpos (by rw [hx]; exact isIntegral_one)
  haveI := finiteDimensional_max_unramified K
  unfold Ks
  exact IntermediateField.finiteDimensional_sup _ _

def bigLL (K LL : FinExt l) : FinExt l :=
  ⟨LL.1 ⊔ IntermediateField.normalClosure ℚ_[l] ↥(Ks K 1) (Om l), by
    have := LL.2
    have := fd_Ks K 1
    exact IntermediateField.finiteDimensional_sup _ _⟩

theorem le_bigLL (K LL : FinExt l) : LL.1 ≤ (bigLL K LL).1 := le_sup_left

theorem unram_of_caseA {K LL : FinExt l} (hA : CaseA K LL) :
    Function.Bijective (algebraMap ↥(K0 K) ↥K.1) := by
  refine ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun y => ⟨⟨y, ⟨y.2, hA.1 y.2⟩⟩, ?_⟩⟩
  apply Subtype.ext
  rfl

def BrRest {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] (W : LocWach PD LL O v n)
    [Fintype (K →ₐ[Qp] LL)] : Prop :=
  ∃ e : W.DD W.one, UnitGen W e ∧ BKExt W e ∧ ∀ hR : Ring9 W, Realised2 hR e

theorem brHyp2_of_rec (P : LocPrime l) {K LL : FinExt l} (hA : CaseA K LL) (h5 : 5 ≤ l)
    [NeZero (finrank ℚ_[l] ↥(K0 K))] [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)]
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (finrank ℚ_[l] ↥(K0 K))) (hs : W.s = 1) {Cc : ℝ}
    (h5W : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h6W : Formalism.MainNotions.DeltaInvariantLattices.WachSaturationExactness W) (h9W : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (h2a : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexFirstProperty W) (hwx : Formalism.MainNotions.LiftingTheory.coreWX W) (hwr : Formalism.MainNotions.LiftingTheory.coreWR W Cc)
    (htools : ToolsAlg W) (hf1 : F1 W) (hf2 : F2 W) (hH : HodgeExact (P.PD K) ↥LL.1 ↥(OL LL))
    (hrest : BrRest W) : BrHyp2 W Cc := by
  refine ⟨hs, unram_of_caseA hA, ?_, h5W, h6W, h9W, h2a, hwx, hwr, htools, hf1, hf2, hH, ?_, ?_, hrest⟩
  · rw [P.PD_p K]
    exact h5
  · unfold ValRing
    refine ⟨fun a b h => Subtype.ext h, fun x hx => ⟨⟨x, (P.v_O LL x).1 hx⟩, rfl⟩, fun o => ?_⟩
    exact (P.v_O LL _).2 o.2
  · rw [P.PD_p K]
    exact complete_OL LL

end Formalism.MainNotions.WachCoordinates.Br
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ModelKStep
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def ExpL (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) (ζ : LL) (x : LA W T π' c)
    (f : ℤ → T.V ⊗[Qp] BdR) : Prop :=
  (∃ m₀ : ℤ, ∀ i < m₀, f i = 0) ∧ ∃ (m : ℕ) (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T), IsRepL W T π' Eπ h' c x a y ∧
    ∀ i, serMul (W.lev c ζ (Eπ ^ h')) f i = expS W T c ζ (fun j => (a j : LetA O n)) y i

abbrev QL (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) : Type :=
  ↥(LamLA W T π' Eπ h' c ⊤) ⧸ (piNL W T Pt π' Eπ h' c 1).comap (LamLA W T π' Eπ h' c ⊤).subtype

def ModelL (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' M : ℕ) (c : ZMod n) : Prop :=
  NL W T Pt π' Eπ h' c ≤ LamLA W T π' Eπ h' c ⊤ ∧
  (∀ x ∈ NL W T Pt π' Eπ h' c, γLA W T π' c x ∈ NL W T Pt π' Eπ h' c) ∧
  (∀ a ∈ W.AΔ, ∀ x ∈ NL W T Pt π' Eπ h' c, smulLA W T π' c a x ∈ NL W T Pt π' Eπ h' c) ∧
  (LinearMap.range (toLA W T π' c ⊤)).map (smulLA W T π' c (Eπ ^ h')) ≤ NL W T Pt π' Eπ h' c ∧
  (∀ x ∈ LamLA W T π' Eπ h' c ⊤, ∀ k : ℕ, ((PD.p : ℕ) : O) ^ k • x ∈ NL W T Pt π' Eπ h' c →
    x ∈ NL W T Pt π' Eπ h' c) ∧
  JLA W T π' Eπ h' M c ≤ piNL W T Pt π' Eπ h' c M ∧
  ∀ x ∈ LamLA W T π' Eπ h' c ⊤, γLA W T π' c x - x ∈ NL W T Pt π' Eπ h' c →
    ∀ τ ζ, Pt c ζ τ → ∀ f, ExpL W T π' Eπ h' c ζ x f → ∀ i : ℤ, i ≠ 0 →
      f i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-i)

def ModelQ (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) : Prop :=
  Module.Finite O (QL W T Pt π' Eπ h' c) ∧
    ∀ (a : O) (q : QL W T Pt π' Eπ h' c), a ≠ 0 → a • q = 0 → q = 0

def ModelK {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (π' : LetA O n) (ρ : ℕ) (c : ZMod n) : Prop :=
  ∀ y ∈ NcS W T₂ (c - 1), ∃ x ∈ NcS W T₁ (c - 1), W.map F x - ((PD.p : ℕ) : O) ^ ρ • y ∈ PiNS W T₂ π' 1

end Local

section Record

def modelLR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ h' : ℕ, 1 ≤ h' → ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      ∀ c, ModelL ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') c

def modelQR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ h' : ℕ, 1 ≤ h' → ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      ∀ c, ModelQ ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c

def modelKR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T₁.ρ →
      IsCrys ((D.loc l).PD K) T₂.ρ → F.Onto → (∀ τ, JumpsInV ((D.loc l).PD K) T₁.ρ τ (Set.Icc (-(h' : ℤ)) h')) → ∀ c, ModelK ((HW l).W K 1 LL hG) F π' (rhoA l (eK K) h') c

end Record

def ModelLStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelLR D HW

def ModelQStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelQR D HW

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.StrictSesLetter
section
noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.Strict

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.TruncatedSeriesCountingBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

section Funct

variable {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} (f : V →ₗ[LL] V')

theorem crisMap_mulVB (c : K₀) (z : V ⊗[Qp] B) :
    crisMap B f (mulVB (LL := LL) (V := V) (B := B) c z) = mulVB (LL := LL) (V := V') (B := B) c (crisMap B f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [crisMap, mulVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mem_DcrisL_iff (τ₀ : K₀ →ₐ[Qp] LL) (z : V ⊗[Qp] B) :
    z ∈ DcrisL PD ρ τ₀ ↔ z ∈ Dcris PD ρ ∧ ∀ c : K₀, mulVB (LL := LL) (V := V) (B := B) c z = τ₀ c • z := by
  simp [DcrisL, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

end Funct

section SES

variable {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

end SES

section P4Y

variable {PD} {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

end P4Y

section Rec

theorem p4YL (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (hL : Formalism.MainNotions.UnusedSlot80.LevCoeff D HW F) :
    Formalism.MainNotions.ArcLiftingSetup.AtCaseA fun l _ K LL hG => Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration ((HW l).W K 1 LL hG) := by
  intro l _ K LL hG hCA h5
  exact hL l K LL hCA h5

end Rec

end Formalism.MainNotions.UnusedSlot80.Strict

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ThetaScalarFamilyOfEigenvalue
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.MainNotions Filter Topology

theorem export_link_of_family {eps : ℝ} (Fm : FamP eps) (h : Formalism.MainNotions.TwistedPlaces.OrbitValuationBound Fm) : LinkN Fm := by
  obtain ⟨C, x0, hx⟩ := h
  refine ⟨C, x0, fun x hx0 i hsha j hj hS => ?_⟩
  have hp := hx x hx0 i
  unfold TwistedPlaces.aux₃ at hp
  exact hp hsha hS j hj

theorem linkN_of {eps : ℝ} (Fm : FamP eps) (hA : Formalism.MainNotions.TwistedPlaces.AdmF Fm) (hS : Formalism.MainNotions.TwistedPlaces.KudlaFamilyStatement Fm) :
    LinkN Fm := export_link_of_family Fm (hS hA)

def ThetaScalarNonzero (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  ∀ σ : D.what₂.FT, ∃ lam : ℂ, lam ≠ 0 ∧ ∀ f ∈ D.what₂.isot j σ,
    D.what₂.thetaP μ j (D.what₂.thetaT μ j f) = lam • f

theorem thetaT_injective (D : D7) (μ : D.what₂.Tup) (j : ℕ) (hI : DirectSum.IsInternal (D.what₂.isot j))
    (h : ThetaScalarNonzero D μ j) : Function.Injective (D.what₂.thetaT μ j) := by
  classical
  choose lam hlam0 hlam using h
  set T : Module.End ℂ (D.what₂.Mj j) := (D.what₂.thetaP μ j).comp (D.what₂.thetaT μ j) with hTdef
  have hsub : ∀ σ, D.what₂.isot j σ ≤ Module.End.eigenspace T (lam σ) := by
    intro σ f hf
    rw [Module.End.mem_eigenspace_iff]
    exact hlam σ f hf
  have htop : (⊤ : Submodule ℂ (D.what₂.Mj j)) ≤ ⨆ (c : ℂ) (_ : c ≠ 0), Module.End.eigenspace T c := by
    rw [← hI.submodule_iSup_eq_top]
    refine iSup_le fun σ => le_trans (hsub σ) ?_
    exact le_iSup₂_of_le (lam σ) (hlam0 σ) le_rfl
  have hind : iSupIndep (Module.End.eigenspace T) := by
    first
      | exact Module.End.eigenspaces_iSupIndep T
      | exact Module.End.eigenspaces_independent T
  have hdis : Disjoint (Module.End.eigenspace T 0) ⊤ := (hind 0).mono_right htop
  have hker : LinearMap.ker T = ⊥ := by
    rw [← Module.End.eigenspace_zero]
    exact disjoint_top.mp hdis
  have hTinj : Function.Injective T := LinearMap.ker_eq_bot.mp hker
  exact Function.Injective.of_comp (f := D.what₂.thetaP μ j) hTinj

def LamPos (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  ∀ σ : D.what₂.FT,
    (∀ f ∈ D.what₂.isot j σ, D.what₂.thetaP μ j (D.what₂.thetaT μ j f) = ((D.what₂.lamP μ j σ : ℝ) : ℂ) • f) ∧
    (D.what₂.isot j σ ≠ ⊥ → 0 < D.what₂.lamP μ j σ)

end Formalism.MainNotions.N

end
end

