module

public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.BasisCombinationMemInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.GradedClassDecomposition
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.DetectPt
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle0011

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.ExistsInvariantLiftAverage
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]

theorem finiteDelta_mul_mem {a b : W.Gam} (ha : a ∈ W.DelF) (hb : b ∈ W.DelF) : a * b ∈ W.DelF := by
  obtain ⟨k, hk, hak⟩ := (W.DelF_def a).1 ha
  obtain ⟨k', hk', hbk⟩ := (W.DelF_def b).1 hb
  refine (W.DelF_def _).2 ⟨k * k', Nat.mul_pos hk hk', ?_⟩
  rw [mul_pow, pow_mul, hak, one_pow, one_mul, mul_comm k k', pow_mul, hbk, one_pow]

theorem finiteDelta_inv_mem {a : W.Gam} (ha : a ∈ W.DelF) : a⁻¹ ∈ W.DelF := by
  obtain ⟨k, hk, hak⟩ := (W.DelF_def a).1 ha
  exact (W.DelF_def _).2 ⟨k, hk, by rw [inv_pow, hak, inv_one]⟩

theorem exists_basis_Delta_fixed_mem_N (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hs : W.s = 1) (hp2 : PD.p ≠ 2)
    (T : LocLat G Qp LL O) (hcr : IsCrys PD T.ρ) :
    ∃ (r : ℕ) (B : Module.Basis (Fin r) W.EE (W.DD T)),
      (∀ j, ∀ δ ∈ W.DelF, W.γD T δ (B j) = B j) ∧ ∀ j, B j ∈ W.N T := by
  obtain ⟨-, ⟨π', E, -, ⟨r, b, hbΔ, huniq, -⟩, -⟩, -⟩ := hP9 T hcr hs hp2
  have hb : ∀ j, b j ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (b j) = b j := fun j =>
    (show b j ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (b j) = b j from hbΔ j)
  obtain ⟨B, hB⟩ := exists_EE_basis_of_lattice hcr b (fun j => (hb j).1) huniq
  exact ⟨r, B, fun j δ hδ => by rw [hB]; exact (hb j).2 δ hδ, fun j => by rw [hB]; exact (hb j).1⟩

theorem isUnit_card_finiteDelta (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hs : W.s = 1) (hp2 : PD.p ≠ 2)
    (T : LocLat G Qp LL O) (hcr : IsCrys PD T.ρ) : IsUnit ((W.DelF.card : ℕ) : W.EE) := by
  have hcard := (hP9 T hcr hs hp2).1
  have h1 : (1 : W.Gam) ∈ W.DelF := (W.DelF_def 1).2 ⟨1, one_pos, one_pow 1⟩
  have hpos : 0 < W.DelF.card := Finset.card_pos.2 ⟨1, h1⟩
  have hp := PD.hp
  have hlt : W.DelF.card < PD.p := by
    rw [hcard]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.sub_lt hp.pos one_pos)
  have hcop : Nat.Coprime W.DelF.card PD.p := Nat.coprime_comm.1
    ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => absurd (Nat.le_of_dvd hpos hd) (not_le.2 hlt))
  have hb := Nat.gcd_eq_gcd_ab W.DelF.card PD.p
  rw [hcop.gcd_eq_one] at hb
  have hb' : ((W.DelF.card : ℕ) : W.EE) * (Nat.gcdA W.DelF.card PD.p : W.EE) =
      1 - ((PD.p : ℕ) : W.EE) * (Nat.gcdB W.DelF.card PD.p : W.EE) := by
    have h2 := congrArg (Int.cast : ℤ → W.EE) hb
    push_cast at h2
    linear_combination -h2
  have hu : IsUnit (1 - ((PD.p : ℕ) : W.EE) * (Nat.gcdB W.DelF.card PD.p : W.EE)) := by
    have hc := W.EE_complete
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    apply IsAdicComplete.le_jacobson_bot (I := Ideal.span {((PD.p : ℕ) : W.EE)})
    rw [sub_sub_cancel_left]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  rw [← hb'] at hu
  exact isUnit_of_mul_isUnit_left hu

theorem exists_lift_of_onto (hs : W.s = 1) (hLem3 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeLengthLemma W)
    (hJ : ∀ T : LocLat G Qp LL O, CrysLat PD T → ∃ M h : ZMod n → ℕ, Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (hc₁ : CrysLat PD T₁) (hc₂ : CrysLat PD T₂)
    (hon : F.Onto) (y : W.DD T₂) (hy : y ∈ W.N T₂) : ∃ w : W.DD T₁, W.map F w = y := by
  obtain ⟨M, h, hJ'⟩ := hJ T₁ hc₁
  have hL := (hLem3 T₁ T₂ F M h hc₁.2.2.2 hc₂.2.2.2 hon hJ').1
  have hX : W.X = letπ := by
    show (W.φA ^ (W.s - 1)) letπ = letπ
    rw [hs]
    rfl
  have hunit : IsUnit (algebraMap (LetA O n) W.EE (W.X ^ (⨆ j, (M j + h j)))) := by
    rw [hX, map_pow]
    exact W.EE_π.pow _
  have hi : ∀ i : ZMod n, ∃ v : W.DD T₁, W.map F v = (letE i : LetA O n) • y := by
    intro i
    obtain ⟨z, -, hz⟩ := hL i _ (Submodule.mem_map_of_mem (f := (letE i : LetA O n) • LinearMap.id) hy)
    refine ⟨(↑hunit.unit⁻¹ : W.EE) • z, ?_⟩
    have hz' : W.map F z = algebraMap (LetA O n) W.EE (W.X ^ (⨆ j, (M j + h j))) •
        (letE i : LetA O n) • y := by
      rw [algebraMap_smul]
      exact hz
    rw [map_smul, hz', smul_smul, hunit.val_inv_mul, one_smul]
  choose v hv using hi
  refine ⟨∑ i, v i, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [hv]
  rw [← Finset.sum_smul, sum_letE, one_smul]

theorem exists_invariant_lift_average (hcu : IsUnit ((W.DelF.card : ℕ) : W.EE)) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (w : W.DD T₁) (y : W.DD T₂)
    (hy : ∀ δ ∈ W.DelF, W.γD T₂ δ y = y) (hw : W.map F w = y) :
    ∃ w' : W.DD T₁, (∀ δ ∈ W.DelF, W.γD T₁ δ w' = w') ∧ W.map F w' = y := by
  refine ⟨(↑hcu.unit⁻¹ : W.EE) • ∑ δ ∈ W.DelF, W.γD T₁ δ w, fun δ' hδ' => ?_, ?_⟩
  · have hγc : W.γE δ' ((W.DelF.card : ℕ) : W.EE) = ((W.DelF.card : ℕ) : W.EE) := map_natCast _ _
    have h1 : W.γE δ' (↑hcu.unit⁻¹ : W.EE) * ↑hcu.unit = 1 := by
      rw [IsUnit.unit_spec]
      calc W.γE δ' (↑hcu.unit⁻¹ : W.EE) * ((W.DelF.card : ℕ) : W.EE)
          = W.γE δ' (↑hcu.unit⁻¹ : W.EE) * W.γE δ' ((W.DelF.card : ℕ) : W.EE) := by rw [hγc]
        _ = W.γE δ' ((↑hcu.unit⁻¹ : W.EE) * ((W.DelF.card : ℕ) : W.EE)) := (map_mul _ _ _).symm
        _ = 1 := by rw [hcu.val_inv_mul, map_one]
    have hinv : W.γE δ' (↑hcu.unit⁻¹ : W.EE) = ↑hcu.unit⁻¹ := by
      calc W.γE δ' (↑hcu.unit⁻¹ : W.EE)
          = W.γE δ' (↑hcu.unit⁻¹ : W.EE) * (↑hcu.unit * ↑hcu.unit⁻¹) := by rw [Units.mul_inv, mul_one]
        _ = ↑hcu.unit⁻¹ := by rw [← mul_assoc, h1, one_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [W.γD_smul, hinv, map_sum]
    congr 1
    simp only [← W.γD_mul]
    exact Finset.sum_nbij' (fun δ => δ' * δ) (fun δ => δ'⁻¹ * δ)
      (fun δ hδ => finiteDelta_mul_mem hδ' hδ) (fun δ hδ => finiteDelta_mul_mem (finiteDelta_inv_mem hδ') hδ)
      (fun δ _ => by group) (fun δ _ => by group) (fun δ _ => rfl)
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum]
    rw [Finset.sum_congr rfl fun δ hδ => by rw [W.map_γ, hw, hy δ hδ]]
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul W.EE, smul_smul, hcu.val_inv_mul, one_smul]

end Formalism.MainNotions.N.Ln03.Pf
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.XPowDvdOfComponents
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

theorem X_pow_dvd_of_components {ι R : Type} [CommRing R] (F : PowerSeries (ι → R)) (e : ℕ)
    (h : ∀ i, PowerSeries.X ^ e ∣ PowerSeries.map (Pi.evalRingHom (fun _ => R) i) F) :
    PowerSeries.X ^ e ∣ F := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  funext i
  have := (PowerSeries.X_pow_dvd_iff.1 (h i)) m hm
  rw [PowerSeries.coeff_map] at this
  simpa using this

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

theorem detect [IsFractionRing O LL] (hP4 : LevelMapHodgeFiltration W) (hSat : Sat W) (hcrys : IsCrys PD T.ρ)
    (hLb : ∀ (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hfree : (latOf C).Free c)
    (ϖ : O) (ell : ℕ)
    (hcompl : ∀ s < ell, ∀ (k : ℕ) (a : PowerSeries O), PowerSeries.X ^ k ∣ rhoL hR c s a →
      ∃ (N : ℕ) (z : PowerSeries O), PowerSeries.C (ϖ ^ N) * a = (baseIdOf hR).Bs.p s ^ k * z)
    (hϖ : ∃ (N : ℕ) (u : O), ((PD.p : ℕ) : O) ^ N = ϖ * u)
    (s : ℕ) (hs : s < ell) (hfilt : IsFilt (FilD W T c s)) (e : ℕ) (y : C.V) (hy : y ∈ (latOf C).N c)
    (h : ∀ (ζ : Rs LL PD.p s) (k : ℤ),
      (⟨Lb.levB T c ζ ⟨C.t c y, hy⟩ k, Lb.mem T c ζ ⟨C.t c y, hy⟩ k⟩ : Dc W T c) ∈
        FilD W T c s ((e : ℤ) - k)) :
    ∃ y' ∈ (latOf C).N c, y = (baseIdOf hR).Bs.p s ^ e • y' := by
  classical
  obtain ⟨r, b, hind, hspan⟩ := hfree
  have hb : ∀ j, b j ∈ (latOf C).N c := fun j => hspan ▸ Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨hfd, hr⟩ := rank_eq hP3 hmod b hind hspan
  have hy' : y ∈ Submodule.span (PowerSeries O) (Set.range b) := hspan.symm ▸ hy
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy'
  have hyN : (⟨C.t c y, hy⟩ : ↥(W.N T)) =
      ∑ j, (baseIdOf hR).d (a j) • (⟨C.t c (b j), hb j⟩ : ↥(W.N T)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    rw [← ha, coord_t_finset_sum]
    exact Finset.sum_congr rfl fun j _ => C.t_smul c (a j) (b j)

  have hdiv : ∀ (ζ : Rs LL PD.p s) (j : Fin r), PowerSeries.X ^ e ∣ W.lev c ζ ((baseIdOf hR).d (a j)) := by
    intro ζ
    have := hfd
    refine detect_pt (FilD W T c s) hfilt hr
      (fun j k => (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ k, Lb.mem T c ζ _ k⟩ : Dc W T c))
      (fun j => ?_) (fun j k => levB_mem_fil hP4 hcrys hLb s ζ _ k)
      (span_classes hP4 hcrys hLb hmod s hfilt ζ b hb hspan)
      (fun j => W.lev c ζ ((baseIdOf hR).d (a j))) e ?_
    · obtain ⟨m, hm⟩ := Lb.supp T c ζ ⟨C.t c (b j), hb j⟩
      exact ⟨m, fun k hk => Subtype.ext (hm k hk)⟩
    · intro k
      have hk := h ζ k
      change ιV PD (LL := LL) (V := T.V) (Lb.levB T c ζ ⟨C.t c y, hy⟩ k) ∈
        FilLev W T c s ((e : ℤ) - k) at hk
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hLb, hyN, map_sum, Finset.sum_apply] at hk
      show ((ιV PD (LL := LL) (V := T.V)).comp (DcrisL PD T.ρ (W.emb c)).subtype)
        (∑ j, ∑ᶠ i : ℕ, PowerSeries.coeff i (W.lev c ζ ((baseIdOf hR).d (a j))) •
          (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ (k - i), Lb.mem T c ζ _ (k - i)⟩ : Dc W T c)) ∈
        FilLev W T c s ((e : ℤ) - k)
      suffices heq : ∀ j, ((ιV PD (LL := LL) (V := T.V)).comp (DcrisL PD T.ρ (W.emb c)).subtype)
          (∑ᶠ i : ℕ, PowerSeries.coeff i (W.lev c ζ ((baseIdOf hR).d (a j))) •
            (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ (k - i), Lb.mem T c ζ _ (k - i)⟩ : Dc W T c)) =
          W.levN T c ζ ((baseIdOf hR).d (a j) • (⟨C.t c (b j), hb j⟩ : ↥(W.N T))) k by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.sum_congr rfl fun j _ => heq j]
        exact hk
      intro j
      rw [W.levN_smul]
      obtain ⟨m, hm⟩ := Lb.supp T c ζ ⟨C.t c (b j), hb j⟩
      have hfin : (Function.support fun i : ℕ => PowerSeries.coeff i (W.lev c ζ ((baseIdOf hR).d (a j))) •
          (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ (k - i), Lb.mem T c ζ _ (k - i)⟩ : Dc W T c)).Finite := by
        refine (Finset.range ((k - m).toNat + 1)).finite_toSet.subset fun i hi => ?_
        rw [Finset.coe_range, Set.mem_Iio]
        by_contra hlt
        apply hi
        have h0 : (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ (k - i), Lb.mem T c ζ _ (k - i)⟩ : Dc W T c) = 0 :=
          Subtype.ext (hm _ (by omega))
        show _ • _ = 0
        rw [h0, smul_zero]
      rw [map_finsum _ hfin]
      refine finsum_congr fun i => ?_
      rw [map_smul, LinearMap.comp_apply, Submodule.subtype_apply, ← hLb]

  have hcj : ∀ j, ∃ (N : ℕ) (z : PowerSeries O),
      PowerSeries.C (ϖ ^ N) * a j = (baseIdOf hR).Bs.p s ^ e * z := by
    intro j
    refine hcompl s hs e (a j) (X_pow_dvd_of_components _ e fun ζ => ?_)
    rw [map_eval_rhoL]
    exact hdiv ζ j
  choose Nj z hz using hcj
  obtain ⟨N', u, hu⟩ := hϖ
  set Nt := ∑ j, Nj j with hNt
  set K := N' * Nt with hK
  have hlK : ∀ j, PowerSeries.C (((PD.p : ℕ) : O) ^ K) * a j =
      (baseIdOf hR).Bs.p s ^ e * (PowerSeries.C (u ^ Nt * ϖ ^ (Nt - Nj j)) * z j) := by
    intro j
    have hle : Nj j ≤ Nt := Finset.single_le_sum (fun j _ => Nat.zero_le (Nj j)) (Finset.mem_univ j)
    have e1 : ((PD.p : ℕ) : O) ^ K = u ^ Nt * ϖ ^ (Nt - Nj j) * ϖ ^ Nj j := by
      rw [hK, pow_mul, hu, mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel hle, mul_comm]
    rw [e1, map_mul, mul_assoc, hz j]
    ring
  set w : C.V := ∑ j, (PowerSeries.C (u ^ Nt * ϖ ^ (Nt - Nj j)) * z j) • b j with hw
  have hwN : w ∈ (latOf C).N c :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hb j)
  have hyw : PowerSeries.C (((PD.p : ℕ) : O) ^ K) • y = (baseIdOf hR).Bs.p s ^ e • w := by
    rw [← ha, Finset.smul_sum, hw, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, smul_smul, hlK j]

  have hd : (baseIdOf hR).d ((baseIdOf hR).Bs.p s ^ e) =
      ∏ s' ∈ Finset.range (s + 1), pS W s' ^ (if s' = s then e else 0) := by
    rw [map_pow, BaseId.d_p, Finset.prod_eq_single s (fun s' _ hs' => by rw [if_neg hs', pow_zero])
      (fun hns => absurd (Finset.mem_range.2 (Nat.lt_succ_self s)) hns), if_pos rfl]
  have hdl : (baseIdOf hR).d (PowerSeries.C (((PD.p : ℕ) : O) ^ K)) = ((PD.p : ℕ) : LetA O n) ^ K := by
    rw [BaseId.d_C, map_pow, map_natCast]
  have hNΔ : ∀ x : W.DD T, x ∈ W.N T → (∀ δ ∈ W.DelF, W.γD T δ x = x) → x ∈ W.NΔ T :=
    fun x h1 h2 => ⟨h1, h2⟩
  have hx : C.t c y ∈ mulSet W T ((baseIdOf hR).d ((baseIdOf hR).Bs.p s ^ e)) (W.NΔ T) := by
    refine hSat T ((baseIdOf hR).d ((baseIdOf hR).Bs.p s ^ e)) 1 hcrys
      ⟨0, (baseIdOf hR).d ((baseIdOf hR).Bs.p s ^ e), ⟨fun s' => if s' = s then e else 0, s + 1, hd⟩, by simp⟩
      ⟨0, 1, ⟨fun _ => 0, 0, by simp⟩, by simp⟩ (C.t c y) (fun δ hδ => C.t_Δ c y δ hδ) ?_ ?_
    · rw [one_smul]
      exact hNΔ _ hy (fun δ hδ => C.t_Δ c y δ hδ)
    · refine ⟨K, C.t c w, hNΔ _ hwN (fun δ hδ => C.t_Δ c w δ hδ), ?_⟩
      rw [← hdl, ← Coord.t_smul, hyw, Coord.t_smul]
  obtain ⟨z', hz', hxz⟩ := hx
  have hlet : (letE c : LetA O n) • ((letE c : LetA O n) • z') = (letE c : LetA O n) • z' := by
    rw [smul_smul, letE_mul_self]
  have hΔ : ∀ δ ∈ W.DelF, W.γD T δ ((letE c : LetA O n) • z') = (letE c : LetA O n) • z' := by
    intro δ hδ
    rw [Formalism.MainNotions.WachCoordinates.Br.γD_smulA, γA_letE, hz'.2 δ hδ]
  obtain ⟨y'', hy''⟩ := C.t_surj c _ hlet hΔ
  refine ⟨y'', ?_, ?_⟩
  · show C.t c y'' ∈ W.N T
    rw [hy'']
    exact (W.N T).smul_mem _ hz'.1
  · apply C.t_inj c
    rw [Coord.t_smul, hy'', smul_smul, mul_comm, ← smul_smul, ← hxz, C.t_letter]

end Formalism.MainNotions.N.Ln03.K8

end
end

