module

public import Formalism.LocalToGlobal.GroupLattices.FockModels.ElementaryDivisorBasis
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.LatticeSystems

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgeLatticeAdaptedBasis
section
open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems Formalism.L2.G.Model

def ordMax {n' m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) : ℤ :=
  ∑ s : Fin n', ∑ a : Fin (m + 1) with a.val < r, (lamAt lam0 s a - lamAt lam0 s (Fin.last m))

theorem pos_basisO (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m r : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det) :
    ∃ (X : ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
      (π : ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) → ℤ),
      LinearIndependent Kf X ∧ Submodule.span Kf (Set.range X) = dualWeyl Kf (m + 1) (m + 1) (nuOf lam) ∧
      (∀ i, π i ≤ ∑ a : Fin (m + 1) with a.val < r, lam a) ∧
      (∀ i, ((Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card : ℤ) * lam (Fin.last m) ≤ π i) ∧
      ∀ c : Kf, c ≠ 0 → Submodule.span O (Set.range fun i => c ^ π i • X i) =
        nablaLTw O Kf m lam (g * lb_D (m + 1) r c) := by
  classical
  obtain ⟨b, hb, hbd⟩ := Formalism.MainNotions.G.LatticeSystems.lb_basis O (m + 1) (m + 1) (nuOf lam)
  obtain ⟨hKi, hKs⟩ := nablaLKBasis O Kf hinj (m + 1) (m + 1) (nuOf lam) b _ hb g hg
  have hdet0 : g.det ≠ 0 := hg.ne_zero
  set ll := lam (Fin.last m) with hll
  set S := Finset.univ.filter fun a : Fin (m + 1) => a.val < r with hS
  set f := fun i : ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) => rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i)) with hf
  have hdg0 : g.det ^ (-ll) ≠ 0 := zpow_ne_zero _ hdet0
  refine ⟨fun i => g.det ^ (-ll) • f i,
    fun i => ((∑ a ∈ S, rowWt i.1 a : ℕ) : ℤ) + (S.card : ℤ) * ll, ?_, ?_, ?_, ?_, ?_⟩
  · exact hKi.units_smul (fun _ => Units.mk0 (g.det ^ (-ll)) hdg0)
  · rw [← Set.smul_set_range, Submodule.span_smul_eq_of_isUnit _ _ (Ne.isUnit hdg0)]
    exact hKs
  · intro i
    have h1 := hbd i r
    have h2 : ((∑ a ∈ S, rowWt i.1 a : ℕ) : ℤ) ≤ ∑ a ∈ S, (lam a - ll) := by
      calc ((∑ a ∈ S, rowWt i.1 a : ℕ) : ℤ) ≤ ((∑ a ∈ S, nuOf lam a : ℕ) : ℤ) := by exact_mod_cast h1
        _ = ∑ a ∈ S, (lam a - ll) := by
          push_cast
          refine Finset.sum_congr rfl fun a _ => ?_
          have : ll ≤ lam a := hlam (Fin.le_last a)
          simp only [nuOf]
          omega
    have h3 : ∑ a ∈ S, (lam a - ll) = ∑ a ∈ S, lam a - (S.card : ℤ) * ll := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    linarith
  · intro i
    have : (0 : ℤ) ≤ ((∑ a ∈ S, rowWt i.1 a : ℕ) : ℤ) := Int.natCast_nonneg _
    linarith
  · intro c hc
    have ht : ∀ a : Fin (m + 1), (if a.val < r then c⁻¹ else 1) ≠ 0 := by
      intro a; split_ifs <;> simp [hc]
    obtain ⟨-, hD⟩ := nablaLDiag O Kf hinj (m + 1) (m + 1) (nuOf lam) b _ hb g _ hg ht
    have hgD : g * lb_D (m + 1) r c =
        g * Matrix.diagonal (fun a : Fin (m + 1) => if a.val < r then c⁻¹ else 1) := rfl
    rw [nablaLTw, hgD]
    change _ = Submodule.map _ (nablaL O Kf (m + 1) (m + 1) (nuOf lam) _)
    rw [← hD, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    have hprod : (∏ a, (if a.val < r then c⁻¹ else 1) ^ rowWt i.1 a)⁻¹ = c ^ (∑ a ∈ S, rowWt i.1 a) := by
      simp_rw [ite_pow, one_pow]
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_pow_eq_pow_sum, inv_pow, inv_inv]
    have hdet : (g * Matrix.diagonal fun a : Fin (m + 1) => if a.val < r then c⁻¹ else 1).det =
        g.det * c⁻¹ ^ S.card := by
      rw [Matrix.det_mul, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const_one, mul_one,
        Finset.prod_const]
    have hpw : (c⁻¹ ^ S.card) ^ (-ll) = c ^ ((S.card : ℤ) * ll) := by
      rw [inv_pow, inv_zpow', ← zpow_natCast, ← zpow_mul]
      ring_nf
    simp only [Function.comp_apply]
    rw [hdet, ← hll, hprod]
    simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, smul_smul]
    congr 1
    rw [mul_zpow, hpw, zpow_add₀ hc, zpow_natCast]
    ring

theorem ten_basisO (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf]
    {n' m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant lam0)
    (gs : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hgs : ∀ s, IsUnit (gs s).det) :
    ∃ (I : Type) (_ : Finite I) (x : Module.Basis I Kf (Vsp Kf lam0)) (π : I → ℤ),
      (∀ i, π i ≤ Ar r lam0) ∧ (∀ i, Ar r lam0 - π i ≤ ordMax r lam0) ∧
      ∀ c : Kf, c ≠ 0 → Submodule.span O (Set.range fun i => c ^ π i • x i) =
        toV lam0 (Hten O lam0 fun s => colSpan O (gs s * lb_D (m + 1) r c)) := by
  classical
  have hinj : Function.Injective (algebraMap O Kf) := IsFractionRing.injective O Kf
  have hinj' : Function.Injective fun a : O => a • (1 : Kf) := by
    have : (fun a : O => a • (1 : Kf)) = algebraMap O Kf :=
      funext fun a => (Algebra.algebraMap_eq_smul_one a).symm
    rw [this]; exact hinj
  have hA : ∀ s, Antitone (lamAt lam0 s) := kp_lamAt_antitone lam0 hd
  have hI := Formalism.MainNotions.G.LatticeSystems.la_indep (O := O) (Kf := Kf) hinj
  have hpos := fun s => pos_basisO O Kf hinj m r (lamAt lam0 s) (hA s) (gs s) (hgs s)
  choose X π hXi hXs hup hlo hspan using hpos
  have : ∀ s, Finite ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s))) :=
    fun s => (sSIdxFinite _ _ _).to_subtype
  have : ∀ s, Fintype ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s))) := fun s => Fintype.ofFinite _
  have : IsFractionRing Kf Kf := jr_KK Kf
  set P : (∀ s : Fin n', ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))) →
      MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf :=
    fun i => ∏ s, blockEmb Kf s (X s (i s)) with hP
  obtain ⟨hPi, hPs⟩ := tensorBasis Kf Kf (Fin n') (m + 1) (m + 1) _ _ X hXi hXs
  have hV : Vsp Kf lam0 = Submodule.span Kf (Set.range P) := by
    rw [hPs]
    simp only [Vsp, hA, ↓reduceIte]
  have hmem : ∀ i, P i ∈ Vsp Kf lam0 := fun i => hV ▸ Submodule.subset_span ⟨i, rfl⟩
  set y : (∀ s : Fin n', ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))) → Vsp Kf lam0 :=
    fun i => ⟨P i, hmem i⟩ with hy
  have hyi : LinearIndependent Kf y := LinearIndependent.of_comp (Vsp Kf lam0).subtype hPi
  have hys : Submodule.span Kf (Set.range y) = ⊤ := by
    rw [eq_top_iff, ← comap_span_coe (O := Kf) (Kf := Kf) (Vsp Kf lam0) y]
    intro v _
    rw [Submodule.mem_comap]
    have hv : (v : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Submodule.span Kf (Set.range P) :=
      hV ▸ v.2
    exact hv
  refine ⟨_, inferInstance, Module.Basis.mk hyi hys.symm.le, fun i => ∑ s, π s (i s), ?_, ?_, ?_⟩
  · intro i
    unfold Ar
    exact Finset.sum_le_sum fun s _ => hup s (i s)
  · intro i
    unfold Ar ordMax
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    linarith [hlo s (i s)]
  · intro c hc
    have hdet : ∀ s, IsUnit (gs s * lb_D (m + 1) r c).det := fun s => by
      rw [Matrix.det_mul]; exact (hgs s).mul (lb_D_det _ _ _ hc)
    have hli : ∀ s, LinearIndependent O fun j => c ^ π s j • X s j := fun s =>
      ((hXi s).units_smul fun j => Units.mk0 (c ^ π s j) (zpow_ne_zero _ hc)).restrict_scalars hinj'
    obtain ⟨-, hT⟩ := tensorBasis O Kf (Fin n') (m + 1) (m + 1) _
      (fun s => Submodule.span O (Set.range fun j => c ^ π s j • X s j)) (fun s j => c ^ π s j • X s j)
      hli (fun s => rfl)
    have hH : Hten O lam0 (fun s => colSpan O (gs s * lb_D (m + 1) r c)) =
        Submodule.span O (Set.range fun i => c ^ (∑ s, π s (i s)) • P i) := by
      have e1 : (fun s => H0 O m (lamAt lam0 s) (colSpan O (gs s * lb_D (m + 1) r c))) =
          fun s => Submodule.span O (Set.range fun j => c ^ π s j • X s j) := by
        funext s
        rw [H0_eq_twisted_nabla hI m _ (hA s) _ (hdet s), hspan s c hc]
      rw [Hten, e1, ← hT]
      congr 2
      funext i
      simp only [map_smul]
      rw [Finset.prod_smul, lb_zpow_sum c hc]
    rw [toV, hH, ← comap_span_coe (O := O) (Kf := Kf) (Vsp Kf lam0)
      (fun i => c ^ (∑ s, π s (i s)) • (Module.Basis.mk hyi hys.symm.le) i)]
    congr 3
    funext i
    rw [Submodule.coe_smul, Module.Basis.mk_apply]

section
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem edge_lattice_adapted_basis (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (hd : IsDominant lam0) (e : Edge W Qq (m + 1)) (he : IsEdge p n' r e) :
    ∃ (I : Type) (_ : Finite I) (x : Module.Basis I Kf ↥(Vsp Kf lam0)) (π : I → ℤ),
      Submodule.span O (Set.range x) = HL ι σ lam0 e.src ∧
      Submodule.span O (Set.range fun i => ((p : Kf) ^ π i) • x i) = HL ι σ lam0 e.tgt ∧
      Submodule.span O (Set.range fun i => (algebraMap O Kf w ^ π i) • x i) = HLe p ι σ w lam0 e ∧
      (∀ i, 0 ≤ order r lam0 (π i)) ∧ (∀ i, order r lam0 (π i) ≤ ordMax r lam0) ∧
      Submodule.span O (Set.range fun i => (algebraMap O Kf w ^ (-order r lam0 (π i))) • x i) =
        Re p ι σ w r lam0 e ∧
      Submodule.span O (Set.range fun i =>
          (algebraMap O Kf w ^ (-order r lam0 (π i)) * (p : Kf) ^ (-π i)) • x.coord i) =
        Re' p ι σ w r lam0 e := by
  classical
  have hw := w_ne h
  have hp := p_eq h
  have hp0 : (p : Kf) ≠ 0 := by rw [hp]; exact pow_ne_zero 2 hw
  have : IsFractionRing O Kf := h.frac_O
  obtain ⟨gs, hgs, hsrc, hLe, htgt⟩ := edgeLat h m r e he
  obtain ⟨I, hI, x, π, hup, hord, hsp⟩ :=
    ten_basisO O Kf r lam0 hd (fun s : Fin n' => gs s.val) (fun s => hgs s.val)
  have h3 : Submodule.span O (Set.range fun i => (algebraMap O Kf w ^ π i) • x i) = HLe p ι σ w lam0 e := by
    rw [HLe, show (fun s : Fin n' => LeAt p ι σ w s.val e) =
      fun s => colSpan O (gs s.val * lb_D (m + 1) r (algebraMap O Kf w)) from funext fun s => hLe s.val]
    exact hsp _ hw
  refine ⟨I, hI, x, π, ?_, ?_, h3, ?_, ?_, ?_, ?_⟩
  · rw [HL, show (fun s : Fin n' => extO O ι σ s.val e.src) = fun s => colSpan O (gs s.val) from
      funext fun s => hsrc s.val]
    simpa [lb_D_one] using hsp 1 one_ne_zero
  · rw [HL, show (fun s : Fin n' => extO O ι σ s.val e.tgt) =
      fun s => colSpan O (gs s.val * lb_D (m + 1) r (p : Kf)) from
      funext fun s => by rw [htgt, Matrix.mul_assoc, lb_D_sq, hp]]
    exact hsp _ hp0
  · intro i
    unfold order
    linarith [hup i]
  · exact hord
  · rw [Re, ← h3, scale_span]
    congr 2
    funext i
    rw [smul_smul, order, ← zpow_add₀ hw]
    congr 2
    ring
  · rw [Re', ← h3, dualLat_span x _ (fun i => zpow_ne_zero _ hw), scale_span]
    congr 2
    funext i
    rw [smul_smul]
    congr 1
    rw [hp, order, ← zpow_neg, ← zpow_natCast (algebraMap O Kf w) 2, ← zpow_mul, ← zpow_add₀ hw,
      ← zpow_add₀ hw]
    congr 1
    push_cast
    ring

theorem Re_le_scale_HL (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (hd : IsDominant lam0) (e : Edge W Qq (m + 1)) (he : IsEdge p n' r e) (M : ℕ) (hM : ordMax r lam0 ≤ M) :
    Re p ι σ w r lam0 e ≤ scale (algebraMap O Kf w ^ (-(M : ℤ))) (HL (O := O) ι σ lam0 e.src) := by
  obtain ⟨I, hI, x, π, hsrc, -, -, -, hmax, hRe, -⟩ := edge_lattice_adapted_basis h m r lam0 hd e he
  have hw := w_ne h
  rw [← hRe, ← hsrc, scale_span, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hk : 0 ≤ (M : ℤ) - order r lam0 (π i) := by linarith [hmax i]
  obtain ⟨k, hk'⟩ := Int.eq_ofNat_of_zero_le hk
  have he' : (algebraMap O Kf w ^ (-order r lam0 (π i))) • x i =
      (w ^ k) • ((algebraMap O Kf w ^ (-(M : ℤ))) • x i) := by
    rw [← algebraMap_smul Kf (w ^ k), smul_smul, map_pow, ← zpow_natCast, ← zpow_add₀ hw]
    congr 2
    omega
  beta_reduce
  rw [SetLike.mem_coe, he']
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end

end Formalism.MainNotions.Pf14
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgeLatticeMulOfWeightSum
section
noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

theorem lamAt_add {n' m : ℕ} (lam mu : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') :
    lamAt (lam + mu) s = lamAt lam s + lamAt mu s := by
  unfold lamAt
  split_ifs
  · rfl
  · funext i
    simp only [Pi.add_apply, neg_add]

theorem Ar_add {n' m : ℕ} (r : ℕ) (lam mu : Fin n' → Fin (m + 1) → ℤ) :
    Ar r (lam + mu) = Ar r lam + Ar r mu := by
  unfold Ar
  simp only [lamAt_add, Pi.add_apply, Finset.sum_add_distrib]

theorem isDominant_add {n' m : ℕ} {lam mu : Fin n' → Fin (m + 1) → ℤ} (h1 : IsDominant lam) (h2 : IsDominant mu) :
    IsDominant (lam + mu) := by
  intro s
  exact (h1 s).add (h2 s)

theorem nuOf_add {m : ℕ} {a b : Fin (m + 1) → ℤ} (ha : Antitone a) (hb : Antitone b) :
    nuOf (a + b) = nuOf a + nuOf b := by
  funext t
  have h1 : 0 ≤ a t - a (Fin.last m) := sub_nonneg.2 (ha (Fin.le_last t))
  have h2 : 0 ≤ b t - b (Fin.last m) := sub_nonneg.2 (hb (Fin.le_last t))
  simp only [nuOf, Pi.add_apply]
  rw [show a t + b t - (a (Fin.last m) + b (Fin.last m)) =
      (a t - a (Fin.last m)) + (b t - b (Fin.last m)) by ring]
  exact Int.toNat_add h1 h2

theorem dualWeyl_mul (R : Type*) [CommRing R] (r n : ℕ) (ν ν' : Fin n → ℕ)
    {F G : MvPolynomial (Fin r × Fin n) R} (hF : F ∈ dualWeyl R r n ν) (hG : G ∈ dualWeyl R r n ν') :
    F * G ∈ dualWeyl R r n (ν + ν') := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hF hG ⊢
  refine ⟨hF.1.mul hG.1, fun l j hlj => ?_⟩
  rw [map_mul, map_mul, hF.2 l j hlj, hG.2 l j hlj]

theorem tensorLat_mul (R K : Type*) [CommRing R] [CommRing K] [Algebra R K] {S : Type*} [Fintype S] {k n : ℕ}
    (M M' M'' : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (h : ∀ s, ∀ F ∈ M s, ∀ G ∈ M' s, F * G ∈ M'' s)
    {x y : MvPolynomial (S × (Fin k × Fin n)) K} (hx : x ∈ tensorLat R K M) (hy : y ∈ tensorLat R K M') :
    x * y ∈ tensorLat R K M'' := by
  have key : tensorLat R K M * tensorLat R K M' ≤ tensorLat R K M'' := by
    unfold tensorLat
    rw [Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨a, ⟨F, hF, rfl⟩, b, ⟨G, hG, rfl⟩, rfl⟩
    refine ⟨fun s => F s * G s, fun s => h s _ (hF s) _ (hG s), ?_⟩
    simp only [map_mul, Finset.prod_mul_distrib]
  exact key (Submodule.mul_mem_mul hx hy)

theorem V_mul (Kf : Type*) [Field Kf] {n' m : ℕ} {lam mu nu : Fin n' → Fin (m + 1) → ℤ} (hnu : nu = lam + mu)
    (h1 : IsDominant lam) (h2 : IsDominant mu)
    {x y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf} (hx : x ∈ Vsp Kf lam) (hy : y ∈ Vsp Kf mu) :
    x * y ∈ Vsp Kf nu := by
  subst hnu
  unfold Vsp at hx hy ⊢
  refine tensorLat_mul Kf Kf _ _ _ ?_ hx hy
  intro s F hF G hG
  have hs := lamAt_add lam mu s
  by_cases ha : Antitone (lamAt lam s)
  · by_cases hb : Antitone (lamAt mu s)
    · have hab : Antitone (lamAt (lam + mu) s) := by
        rw [hs]
        exact ha.add hb
      rw [if_pos ha] at hF
      rw [if_pos hb] at hG
      rw [if_pos hab, hs, nuOf_add ha hb]
      exact dualWeyl_mul Kf (m + 1) (m + 1) _ _ hF hG
    · rw [if_neg hb, Submodule.mem_bot] at hG
      rw [hG, mul_zero]
      exact Submodule.zero_mem _
  · rw [if_neg ha, Submodule.mem_bot] at hF
    rw [hF, zero_mul]
    exact Submodule.zero_mem _

def mulV {Kf : Type*} [Field Kf] {n' m : ℕ} {lam mu nu : Fin n' → Fin (m + 1) → ℤ} (hnu : nu = lam + mu)
    (h1 : IsDominant lam) (h2 : IsDominant mu) (x : Vsp Kf lam) (y : Vsp Kf mu) : Vsp Kf nu :=
  ⟨(x : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * y, V_mul Kf hnu h1 h2 x.2 y.2⟩

@[simp] theorem mulV_coe {Kf : Type*} [Field Kf] {n' m : ℕ} {lam mu nu : Fin n' → Fin (m + 1) → ℤ}
    (hnu : nu = lam + mu) (h1 : IsDominant lam) (h2 : IsDominant mu) (x : Vsp Kf lam) (y : Vsp Kf mu) :
    ((mulV hnu h1 h2 x y : Vsp Kf nu) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = x * y := rfl

section Scale

variable {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
  [IsScalarTower O Kf X]

theorem scale_scale (a b : Kf) (M : Submodule O X) : scale a (scale b M) = scale (a * b) M := by
  unfold scale
  rw [← Submodule.map_comp]
  congr 1
  ext x
  show a • (b • x) = (a * b) • x
  rw [mul_smul]

end Scale

section Lat

variable {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ}

theorem toV_mul (D : Formalism.BasicNotions.D7) (hM : tableLineDegreeFive.LevelPrimesProviso D) {lam mu nu : Fin n' → Fin (m + 1) → ℤ} (hnu : nu = lam + mu)
    (h1 : IsDominant lam) (h2 : IsDominant mu) (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf)) (α β : Kf)
    {x : Vsp Kf lam} {y : Vsp Kf mu} {z : Vsp Kf nu}
    (hz : (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = x * y)
    (hx : x ∈ scale α (toV lam (Hten O lam Λ))) (hy : y ∈ scale β (toV mu (Hten O mu Λ))) :
    z ∈ scale (α * β) (toV nu (Hten O nu Λ)) := by
  subst hnu
  obtain ⟨x0, hx0, rfl⟩ := Submodule.mem_map.1 hx
  obtain ⟨y0, hy0, rfl⟩ := Submodule.mem_map.1 hy
  have hmem : ((x0 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * y0) ∈ Hten O (lam + mu) Λ :=
    hM O Kf n' m lam mu Λ h1 h2 _ (Submodule.mem_comap.1 hx0) _ (Submodule.mem_comap.1 hy0)
  refine Submodule.mem_map.2 ⟨⟨(x0 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * y0,
    V_mul Kf rfl h1 h2 x0.2 y0.2⟩, hmem, ?_⟩
  apply Subtype.ext
  rw [hz]
  show (α * β) • ((x0 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
      (y0 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) =
    (α • (x0 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) * (β • (y0 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf))
  rw [smul_mul_smul_comm]

variable {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

theorem HL_mul (D : Formalism.BasicNotions.D7) (hM : tableLineDegreeFive.LevelPrimesProviso D) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq)
    {lam mu nu : Fin n' → Fin (m + 1) → ℤ} (hnu : nu = lam + mu)
    (h1 : IsDominant lam) (h2 : IsDominant mu) (L : Submodule W (Fin (m + 1) → Qq)) (c : Kf) (hc : c ≠ 0) (a b : ℤ)
    {x : Vsp Kf lam} {y : Vsp Kf mu} {z : Vsp Kf nu}
    (hz : (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = x * y)
    (hx : x ∈ scale (c ^ a) (HL (O := O) ι σ lam L)) (hy : y ∈ scale (c ^ b) (HL (O := O) ι σ mu L)) :
    z ∈ scale (c ^ (a + b)) (HL (O := O) ι σ nu L) := by
  rw [zpow_add₀ hc]
  exact toV_mul D hM hnu h1 h2 _ _ _ hz hx hy

theorem Re_mul (D : Formalism.BasicNotions.D7) (hM : tableLineDegreeFive.LevelPrimesProviso D) (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O)
    (hw : algebraMap O Kf w ≠ 0) (r : ℕ)
    {lam mu nu : Fin n' → Fin (m + 1) → ℤ} (hnu : nu = lam + mu)
    (h1 : IsDominant lam) (h2 : IsDominant mu) (e : Edge W Qq (m + 1)) (a b : ℤ)
    {x : Vsp Kf lam} {y : Vsp Kf mu} {z : Vsp Kf nu}
    (hz : (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = x * y)
    (hx : x ∈ scale (algebraMap O Kf w ^ a) (Re p ι σ w r lam e))
    (hy : y ∈ scale (algebraMap O Kf w ^ b) (Re p ι σ w r mu e)) :
    z ∈ scale (algebraMap O Kf w ^ (a + b)) (Re p ι σ w r nu e) := by
  subst hnu
  unfold Re HLe at hx hy ⊢
  rw [scale_scale] at hx hy ⊢
  have hz' := toV_mul D hM rfl h1 h2 _ _ _ hz hx hy
  convert hz' using 2
  rw [Ar_add, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw]
  congr 1
  ring

theorem edge_lattice_mul_of_weight_sum (D : Formalism.BasicNotions.D7) (hM : tableLineDegreeFive.LevelPrimesProviso D) (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O)
    (hw : algebraMap O Kf w ≠ 0) (r : ℕ)
    {lam mu nu : Fin n' → Fin (m + 1) → ℤ} (hnu : nu = lam + mu)
    (h1 : IsDominant lam) (h2 : IsDominant mu) (e : Edge W Qq (m + 1))
    {x : Vsp Kf lam} {y : Vsp Kf mu} {z : Vsp Kf nu}
    (hz : (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = x * y)
    (hx : x ∈ Re p ι σ w r lam e) (hy : y ∈ Re p ι σ w r mu e) : z ∈ Re p ι σ w r nu e := by
  have h1s : ∀ {lam0 : Fin n' → Fin (m + 1) → ℤ} (M : Submodule O (Vsp Kf lam0)), scale (1 : Kf) M = M := by
    intro lam0 M
    unfold scale
    have hid : (LinearMap.lsmul Kf (Vsp Kf lam0) (1 : Kf)).restrictScalars O = LinearMap.id :=
      LinearMap.ext fun v => by simp
    rw [hid, Submodule.map_id]
  have := Re_mul D hM p ι σ w hw r hnu h1 h2 e 0 0 hz (by rw [zpow_zero, h1s]; exact hx)
    (by rw [zpow_zero, h1s]; exact hy)
  rwa [add_zero, zpow_zero, h1s] at this

end Lat

end Formalism.MainNotions.Pf14
end
end

