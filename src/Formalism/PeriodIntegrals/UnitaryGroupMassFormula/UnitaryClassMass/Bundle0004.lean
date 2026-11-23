module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle0003
public import Formalism.PeriodIntegrals.Bundle0012

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.GmapLeLocS
section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory PI.UnitaryGroupMassFormula.UJClassFin

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Glob

variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V] {M : ℕ}

private theorem mem_locS_iff' (S : Submonoid (𝓞 E)) (X : Submodule (𝓞 E) V) (x : V) :
    x ∈ locS S X ↔ ∃ s ∈ S, s • x ∈ X := Iff.rfl

theorem locS_mono (S : Submonoid (𝓞 E)) {X Y : Submodule (𝓞 E) V} (h : X ≤ Y) : locS S X ≤ locS S Y := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := hx
  exact (mem_locS_iff' S Y x).2 ⟨s, hs, h hx⟩

theorem le_locS (S : Submonoid (𝓞 E)) (X : Submodule (𝓞 E) V) : X ≤ locS S X := fun x hx => (mem_locS_iff' S X x).2 ⟨1, S.one_mem, by simpa using hx⟩

theorem locS_locS (S : Submonoid (𝓞 E)) (X : Submodule (𝓞 E) V) : locS S (locS S X) = locS S X := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, t, ht, hx⟩ := hx
    exact (mem_locS_iff' S X x).2 ⟨t * s, S.mul_mem ht hs, by rwa [mul_smul]⟩
  · exact le_locS S _

theorem locS_eq_of (S : Submonoid (𝓞 E)) {X Y : Submodule (𝓞 E) V} (h1 : X ≤ locS S Y) (h2 : Y ≤ locS S X) :
    locS S X = locS S Y := le_antisymm ((locS_mono S h1).trans (locS_locS S Y).le) ((locS_mono S h2).trans (locS_locS S X).le)

theorem osmul_comm (u : V ≃ₗ[E] V) (s : 𝓞 E) (w : V) : u (s • w) = s • u w := by
  rw [← algebraMap_smul E s w, map_smul, algebraMap_smul]

theorem gmap_locS (u : V ≃ₗ[E] V) (S : Submonoid (𝓞 E)) (X : Submodule (𝓞 E) V) :
    gmap u (locS S X) = locS S (gmap u X) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    mem_locS_iff']
  constructor
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    exact ⟨s, hs, s • y, hy, osmul_comm u s y⟩
  · rintro ⟨s, hs, z, hz, hzx⟩
    refine ⟨u.symm x, ⟨s, hs, ?_⟩, by simp⟩
    have hsz : s • u.symm x = z := by
      apply u.injective
      rw [osmul_comm, LinearEquiv.apply_symm_apply, hzx]
    rw [hsz]
    exact hz

theorem gmap_comp (u w : V ≃ₗ[E] V) (X : Submodule (𝓞 E) V) : gmap (u * w) X = gmap u (gmap w X) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨w y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩

theorem gmap_le_locS (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (S : Submonoid (𝓞 E))
    (K : GL (Fin M) E)
    (h : ∀ x ∈ crdOf b L0, ∃ s ∈ S, (algebraMap (𝓞 E) E s) • (K : Matrix (Fin M) (Fin M) E).mulVec x ∈ crdOf b L0) :
    gmap (linOf b K) L0 ≤ locS S L0 := by
  intro y hy
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hy
  obtain ⟨v, hv, rfl⟩ := hy
  have hx : (b.repr v : Fin M → E) ∈ crdOf b L0 := by
    show ∑ i, b.repr v i • b i ∈ L0
    rw [b.sum_repr]
    exact hv
  obtain ⟨s, hs, hK⟩ := h _ hx
  refine (mem_locS_iff' S L0 _).2 ⟨s, hs, ?_⟩
  have e : linOf b K v = ∑ j, ((K : Matrix (Fin M) (Fin M) E).mulVec (b.repr v)) j • b j := by
    simp only [linOf, LinearEquiv.ofLinear_apply, Matrix.toLin_apply]
  have hK' : ∑ i, ((algebraMap (𝓞 E) E s) • ((K : Matrix (Fin M) (Fin M) E).mulVec (b.repr v))) i • b i ∈ L0 := hK
  rw [e, ← algebraMap_smul E s, Finset.smul_sum]
  convert hK' using 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_smul]

private theorem sum_mem_crdOf (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {ι : Type}
    (t : Finset ι) (z : ι → Fin M → E) (hz : ∀ i ∈ t, z i ∈ crdOf b L0) :
    ∑ i ∈ t, z i ∈ crdOf b L0 := by
  show ∑ j, (∑ i ∈ t, z i) j • b j ∈ L0
  simp only [Finset.sum_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact L0.sum_mem fun i hi => hz i hi

private theorem algebraMap_smul_mem_crdOf (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (s : 𝓞 E)
    {x : Fin M → E} (hx : x ∈ crdOf b L0) : (algebraMap (𝓞 E) E s) • x ∈ crdOf b L0 := by
  show ∑ j, ((algebraMap (𝓞 E) E s) • x) j • b j ∈ L0
  have h := L0.smul_mem s (show ∑ j, x j • b j ∈ L0 from hx)
  rw [Finset.smul_sum] at h
  convert h using 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_smul, algebraMap_smul]

private theorem add_mem_crdOf (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V)
    {x y : Fin M → E} (hx : x ∈ crdOf b L0) (hy : y ∈ crdOf b L0) : x + y ∈ crdOf b L0 := by
  show ∑ j, (x + y) j • b j ∈ L0
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  exact L0.add_mem hx hy

theorem glob_stab {F : Type} [Field F] [Algebra F E] (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V)
    {u k : ℕ} (hu : ∀ x ∈ crdOf b L0, ∀ i, IsIntegral ℤ ((u : F) • x i))
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ crdOf b L0)
    (Y : Matrix (Fin M) (Fin M) E) (s : 𝓞 E) (e : Fin M → Fin M → E) (he : ∀ i j, IsIntegral ℤ (e i j))
    (hY : ∀ i j, (algebraMap (𝓞 E) E s) * (Y - 1) i j = ((u * k : ℕ) : E) * e i j)
    {x : Fin M → E} (hx : x ∈ crdOf b L0) : (algebraMap (𝓞 E) E s) • Y.mulVec x ∈ crdOf b L0 := by
  have key : ∀ i0, (algebraMap (𝓞 E) E s) * (Y.mulVec x) i0 =
      (algebraMap (𝓞 E) E s) * x i0 + ∑ j, ((k : F) • (e i0 j * ((u : F) • x j))) := by
    intro i0
    have hsplit : ∀ j, (algebraMap (𝓞 E) E s) * Y i0 j =
        ((u * k : ℕ) : E) * e i0 j + (algebraMap (𝓞 E) E s) * (1 : Matrix (Fin M) (Fin M) E) i0 j := by
      intro j
      have hj := hY i0 j
      rw [Matrix.sub_apply, mul_sub] at hj
      linear_combination hj
    show (algebraMap (𝓞 E) E s) * ∑ j, Y i0 j * x j = _
    simp only [Finset.mul_sum, ← mul_assoc, hsplit, add_mul, Finset.sum_add_distrib, Matrix.one_apply,
      mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Algebra.smul_def, map_natCast]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hvec : (algebraMap (𝓞 E) E s) • Y.mulVec x = (algebraMap (𝓞 E) E s) • x +
      ∑ i, ∑ j, Pi.single i ((k : F) • (e i j * ((u : F) • x j))) := by
    funext i0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [key i0]
    congr 1
    simp only [Finset.sum_apply, Pi.single_apply]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hvec]
  exact add_mem_crdOf b L0 (algebraMap_smul_mem_crdOf b L0 s hx)
    (sum_mem_crdOf b L0 _ _ fun i _ => sum_mem_crdOf b L0 _ _ fun j _ =>
      hk i _ ((he i j).mul (hu x hx j)))

end Glob

end PI.UnitaryGroupMassFormula.UJClassMass
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LsLat
section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem lsLat : LSLat := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig g
  set L := crdOf b L0 with hLdef
  obtain ⟨⟨c1, hc1, hup⟩, ⟨c2, hc2, hlow⟩⟩ := crdBounds F E V M b L0 hL
  obtain ⟨u, hu, hu'⟩ := up_nat L ⟨c1, hc1, hup⟩
  obtain ⟨k, hk, hk'⟩ := low_nat L ⟨c2, hc2, hlow⟩
  set P := finMat σ (gramOf h b) g⁻¹ with hP
  set Q := finMat σ (gramOf h b) g with hQ
  have hQP : Q * P = 1 := by rw [hQ, hP, ← finMat_mul, mul_inv_cancel, finMat_one]

  have hsm : ∀ e : E, IsIntegral ℤ e → ∀ x ∈ abelian₂ σ (gramOf h b) L g, e • x ∈ abelian₂ σ (gramOf h b) L g := by
    intro e he x hx
    show P.mulVec (vinc (F := F) (e • x)) ∈ latHat F E L
    rw [vinc_smul, Matrix.mulVec_smul]
    exact latHat_incl_smul b L0 he hx
  let C : Submodule (𝓞 E) (Fin M → E) :=
    { carrier := abelian₂ σ (gramOf h b) L g
      add_mem' := fun {x y} hx hy => (LamG σ (gramOf h b) L g).add_mem hx hy
      zero_mem' := (LamG σ (gramOf h b) L g).zero_mem
      smul_mem' := fun c x hx => by
        show (algebraMap (𝓞 E) E c) • x ∈ abelian₂ σ (gramOf h b) L g
        exact hsm _ c.isIntegral_coe x hx }

  obtain ⟨m, hm, hmO⟩ := den_mat (F := F) (E := E) Q
  have hupC : ∀ y ∈ C, ∀ j, IsIntegral ℤ (((m * u : ℕ) : E) * y j) := by
    intro y hy j
    apply oh_inter (F := F)
    have hw : P.mulVec (vinc (F := F) y) ∈ latHat F E L := hy
    have ev : vinc (F := F) y = Q.mulVec (P.mulVec (vinc (F := F) y)) := by
      rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
    have e1 : inclR (F := F) (Af F) (((m * u : ℕ) : E) * y j) =
        ∑ l, (m • Q j l) * (u • P.mulVec (vinc (F := F) y) l) := by
      have : inclR (F := F) (Af F) (((m * u : ℕ) : E) * y j) = (m * u) • vinc (F := F) y j := by
        simp [vinc, nsmul_eq_mul]
      have gen : ∀ w : Fin M → Af F ⊗[F] E,
          (m * u) • Q.mulVec w j = ∑ l, (m • Q j l) * (u • w l) := by
        intro w
        simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, nsmul_eq_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        push_cast
        ring
      rw [this, ← gen, ← ev]
    rw [e1]
    exact AddSubgroup.sum_mem _ fun l _ => Oh_mul (hmO j l) (up_Oh L hu' hw l)
  have hCfg : C.FG := fg_of_den C (m * u) (Nat.mul_pos hm hu) hupC

  obtain ⟨m', hm', hmO'⟩ := den_mat (F := F) (E := E) P
  set c : E := ((k * m' : ℕ) : E) with hc
  have hcne : c ≠ 0 := by rw [hc]; exact_mod_cast (Nat.mul_pos hk hm').ne'
  have hlowC : ∀ i, (Pi.single i c : Fin M → E) ∈ abelian₂ σ (gramOf h b) L g := by
    intro i
    show P.mulVec (vinc (F := F) (Pi.single i c)) ∈ latHat F E L
    have e1 : vinc (F := F) (Pi.single i c) = Pi.single i (inclR (F := F) (Af F) c) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [vinc]
      · simp [vinc, Pi.single_apply, hj]
    have e2 : P.mulVec (Pi.single i (inclR (F := F) (Af F) c)) = k • fun l => m' • P l i := by
      rw [mulVec_single']
      funext l
      simp only [Pi.smul_apply, hc, map_natCast, nsmul_eq_mul]
      push_cast
      ring
    rw [e1, e2]
    exact low_vec L hk' fun l => hmO' l i

  let f : (Fin M → E) →ₗ[𝓞 E] V := (b.equivFun.symm : (Fin M → E) →ₗ[E] V).restrictScalars (𝓞 E)
  let N : Submodule (𝓞 E) V := C.map f
  have hNset : (N : Set V) = latSet σ (gramOf h b) b L0 g := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      show b.equivFun (b.equivFun.symm x) ∈ abelian₂ σ (gramOf h b) L g
      rw [LinearEquiv.apply_symm_apply]; exact hx
    · intro hv
      exact ⟨b.equivFun v, hv, by simp [f]⟩
  have hNfull : Submodule.IsFullLattice E N := by
    refine { toIsLattice := Submodule.IsLattice.of_fg E (hCfg.map f), span_eq_top := ?_ }
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hb : c • b i ∈ (N : Set V) := by
      rw [hNset]
      show b.equivFun (c • b i) ∈ abelian₂ σ (gramOf h b) L g
      have hcrd : b.equivFun (c • b i) = Pi.single i c := by
        funext j
        rw [LinearEquiv.map_smul, Pi.smul_apply, b.equivFun_self]
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj, Ne.symm hj]
      rw [hcrd]
      exact hlowC i
    have hi : b i = c⁻¹ • (c • b i) := by rw [smul_smul, inv_mul_cancel₀ hcne, one_smul]
    rw [hi]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hb)
  exact ⟨N, hNset, hNfull⟩

end PI.UnitaryGroupMassFormula.UJClassMass
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.OneSubEvTInvInt
section
open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct RestrictedProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Ad

open Classical

variable {F : Type} [Field F] [NumberField F]

theorem af_ext {a b : Af F} (h : ∀ w, a w = b w) : a = b := Subtype.ext (funext h)

theorem af_mul_apply (a b : Af F) (w : HeightOneSpectrum (𝓞 F)) : (a * b) w = a w * b w := rfl
theorem af_add_apply (a b : Af F) (w : HeightOneSpectrum (𝓞 F)) : (a + b) w = a w + b w := rfl
theorem af_sub_apply (a b : Af F) (w : HeightOneSpectrum (𝓞 F)) : (a - b) w = a w - b w := rfl
theorem af_one_apply (w : HeightOneSpectrum (𝓞 F)) : (1 : Af F) w = 1 := rfl
theorem af_alg_apply (c : F) (w : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (Af F) c) w = algebraMap F (w.adicCompletion F) c := rfl

variable (v : HeightOneSpectrum (𝓞 F))

def sgl (x : Fv F v) : Af F :=
  RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v x

theorem sgl_apply (x : Fv F v) (w : HeightOneSpectrum (𝓞 F)) : sgl v x w = Pi.single v x w := rfl

theorem sgl_mul (x y : Fv F v) : sgl v (x * y) = sgl v x * sgl v y := af_ext fun w => by
  rw [af_mul_apply, sgl_apply, sgl_apply, sgl_apply]
  by_cases hw : w = v
  · subst hw; rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, mul_zero]

theorem sgl_add (x y : Fv F v) : sgl v (x + y) = sgl v x + sgl v y := af_ext fun w => by
  rw [af_add_apply, sgl_apply, sgl_apply, sgl_apply]
  by_cases hw : w = v
  · subst hw; rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, add_zero]

theorem sgl_smul (c : F) (x : Fv F v) : c • sgl v x = sgl v (c • x) := af_ext fun w => by
  rw [Algebra.smul_def, Algebra.smul_def, af_mul_apply, af_alg_apply, sgl_apply, sgl_apply]
  by_cases hw : w = v
  · subst hw; rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, mul_zero]

theorem sgl_int {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) : sgl v x ∈ intAf F := by
  intro w
  show sgl v x w ∈ w.adicCompletionIntegers F
  rw [sgl_apply]
  by_cases hw : w = v
  · subst hw; rw [Pi.single_eq_same]; exact hx
  · rw [Pi.single_eq_of_ne hw]; exact zero_mem _

theorem sgl_one_mul (a : Af F) : sgl v 1 * a = sgl v (a v) := af_ext fun w => by
  rw [af_mul_apply, sgl_apply, sgl_apply]
  by_cases hw : w = v
  · subst hw; rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
  · rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, zero_mul]

def ivL : Fv F v →ₗ[F] Af F where
  toFun := sgl v
  map_add' := sgl_add v
  map_smul' c x := (sgl_smul v c x).symm

def evT (T : Set (HeightOneSpectrum (𝓞 F))) : Af F :=
  (⟨fun w => if w ∈ T then (1 : w.adicCompletion F) else 0,
    Filter.Eventually.of_forall fun w => by
      show (if w ∈ T then (1 : w.adicCompletion F) else 0) ∈ w.adicCompletionIntegers F
      split_ifs
      · exact one_mem _
      · exact zero_mem _⟩ :
    Πʳ w : HeightOneSpectrum (𝓞 F), [w.adicCompletion F, w.adicCompletionIntegers F])

theorem evT_apply (T : Set (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F)) :
    evT T w = if w ∈ T then 1 else 0 := rfl

theorem evT_int (T : Set (HeightOneSpectrum (𝓞 F))) : evT T ∈ intAf F := by
  intro w
  show evT T w ∈ w.adicCompletionIntegers F
  rw [evT_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem evT_eq_sum (T : Finset (HeightOneSpectrum (𝓞 F))) : evT (T : Set _) = ∑ w ∈ T, sgl w 1 := by
  apply af_ext
  intro w
  set_option synthInstance.maxHeartbeats 100000 in
    rw [evT_apply, show (∑ w' ∈ T, sgl w' 1) w = evalV F w (∑ w' ∈ T, sgl w' 1) from rfl, map_sum]
  simp only [show ∀ w', evalV F w (sgl w' 1) = Pi.single w' 1 w from fun _ => rfl]
  by_cases hw : w ∈ T
  · rw [if_pos (by exact_mod_cast hw), Finset.sum_eq_single w]
    · simp
    · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
    · intro h; exact absurd hw h
  · rw [if_neg (by exact_mod_cast hw)]
    refine (Finset.sum_eq_zero fun b hb => ?_).symm
    have : w ≠ b := fun h => hw (h ▸ hb)
    simp [Pi.single_apply, this]

theorem one_sub_evT_inv_int (T : Set (HeightOneSpectrum (𝓞 F))) (t : 𝓞 F)
    (ht : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ T → t ∉ w.asIdeal) :
    (1 - evT T) * algebraMap F (Af F) ((algebraMap (𝓞 F) F t)⁻¹) ∈ intAf F := by
  intro w
  show ((1 - evT T) * algebraMap F (Af F) ((algebraMap (𝓞 F) F t)⁻¹)) w ∈ w.adicCompletionIntegers F
  rw [af_mul_apply, af_sub_apply, evT_apply, af_one_apply, af_alg_apply]
  split_ifs with hw
  · rw [sub_self, zero_mul]; exact zero_mem _
  · rw [sub_zero, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers]
    have e1 : algebraMap F (w.adicCompletion F) ((algebraMap (𝓞 F) F t)⁻¹) =
        (((algebraMap (𝓞 F) F t)⁻¹ : F) : w.adicCompletion F) := rfl
    rw [e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀,
      HeightOneSpectrum.valuation_of_algebraMap,
      (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w t).2 (ht w hw), inv_one]

end Ad

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))

def Psi : Af F ⊗[F] E →ₐ[F] E ⊗[F] Fv F v :=
  (Algebra.TensorProduct.comm F (Fv F v) E).toAlgHom.comp
    (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E))

theorem Psi_tmul (a : Af F) (e : E) : Psi (E := E) v (a ⊗ₜ[F] e) = e ⊗ₜ[F] a v := by
  simp [Psi]; rfl

def Phi : E ⊗[F] Fv F v →ₗ[F] Af F ⊗[F] E :=
  (TensorProduct.map (ivL v) LinearMap.id) ∘ₗ (TensorProduct.comm F E (Fv F v)).toLinearMap

theorem Phi_tmul (e : E) (x : Fv F v) : Phi v (e ⊗ₜ[F] x) = sgl v x ⊗ₜ[F] e := by
  simp [Phi]; rfl

theorem Phi_Psi (r : Af F ⊗[F] E) : Phi v (Psi v r) = (sgl v 1 ⊗ₜ[F] (1 : E)) * r := by
  induction r using TensorProduct.inductionOn with
  | tmul a e =>
    rw [Psi_tmul, Phi_tmul, Algebra.TensorProduct.tmul_mul_tmul, sgl_one_mul, one_mul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, mul_add]

theorem Phi_mul (x y : E ⊗[F] Fv F v) : Phi v (x * y) = Phi v x * Phi v y := by
  induction x using TensorProduct.inductionOn with
  | tmul e a =>
    induction y using TensorProduct.inductionOn with
    | tmul e' a' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, Phi_tmul, Phi_tmul, Phi_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, sgl_mul]
    | add y y' hy hy' => rw [mul_add, map_add (f := _), hy, hy', map_add (f := _), mul_add]
  | add x x' hx hx' => rw [add_mul, map_add (f := _), hx, hx', map_add (f := _), add_mul]

theorem Phi_inclE (e : E) : Phi v (PI.UnitaryApproxDefs.inclE (F := F) (Fv F v) e) = sgl v 1 ⊗ₜ[F] e := by
  show Phi v (e ⊗ₜ[F] (1 : Fv F v)) = _
  rw [Phi_tmul]

theorem Phi_int {s : E ⊗[F] Fv F v}
    (hs : s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (Fv F v) (PI.UnitaryApproxDefs.intOE E) (v.adicCompletionIntegers F).toSubring) :
    Phi v s ∈ Oh F E := by
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
    · obtain ⟨o, rfl⟩ := he
      rw [Phi_tmul]
      exact tmul_mem_Oh (sgl_int v (one_mem _)) o.isIntegral_coe
    · rw [Phi_tmul]
      exact tmul_mem_Oh (sgl_int v hy) isIntegral_one
  | zero => rw [map_zero]; exact zero_mem _
  | one =>
    rw [show (1 : E ⊗[F] Fv F v) = (1 : E) ⊗ₜ[F] (1 : Fv F v) from rfl, Phi_tmul]
    exact tmul_mem_Oh (sgl_int v (one_mem _)) isIntegral_one
  | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | neg x _ h1 => rw [map_neg]; exact neg_mem h1
  | mul x y _ _ h1 h2 => rw [Phi_mul]; exact Oh_mul h1 h2

end Tens

end PI.UnitaryGroupMassFormula.UJClassMass
end
end

