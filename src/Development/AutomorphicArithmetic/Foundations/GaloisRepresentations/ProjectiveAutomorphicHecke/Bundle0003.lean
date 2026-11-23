module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.ExistsOpenAvoid
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap.PNbhd2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem exists_open_avoid (w : Plc E) (x : GLw n w) (hx : x ≠ 1) :
    ∃ V : Subgroup (GLw n w), IsOpen (V : Set (GLw n w)) ∧ V ≤ GlobalTheory.LFun.KGL w (n := n) ∧ x ∉ V := by
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  by_cases hxK : x ∈ GlobalTheory.LFun.KGL w (n := n)
  swap
  · exact ⟨_, hKo, le_rfl, hxK⟩
  have hne : ∃ i j, x.val i j ≠ (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j := by
    by_contra h
    push_neg at h
    exact hx (Units.ext (Matrix.ext h))
  obtain ⟨i, j, hij⟩ := hne
  haveI : CompactSpace ↥(GlobalTheory.LFun.KGL w (n := n)) := isCompact_iff_compactSpace.1 hKc
  let f : ↥(GlobalTheory.LFun.KGL w (n := n)) → w.adicCompletion E :=
    fun g => g.1.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j
  have hf : Continuous f :=
    Continuous.sub (Continuous.matrix_elem (Units.continuous_val.comp continuous_subtype_val) i j) continuous_const
  obtain ⟨A, hA⟩ := NonarchimedeanAddGroup.is_nonarchimedean
    ({x.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j}ᶜ : Set (w.adicCompletion E))
    (isOpen_compl_singleton.mem_nhds (by simpa using (sub_ne_zero.2 hij).symm))
  have hW : IsClopen (f ⁻¹' (A : Set (w.adicCompletion E))) := A.isClopen.preimage hf
  have h1 : (1 : ↥(GlobalTheory.LFun.KGL w (n := n))) ∈ f ⁻¹' (A : Set (w.adicCompletion E)) := by
    simp [f, A.zero_mem]
  obtain ⟨H, hH⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hW h1
  refine ⟨(H : Subgroup _).map (GlobalTheory.LFun.KGL w (n := n)).subtype, ?_, Subgroup.map_subtype_le _, ?_⟩
  · exact hKo.isOpenEmbedding_subtypeVal.isOpenMap _ H.isOpen
  · rintro ⟨h, hh, rfl⟩
    exact hA (hH hh) rfl

private theorem exists_Kw
    (F : Finset (Σ w : Plc E, {V : Subgroup (GLw n w) // IsOpen (V : Set (GLw n w)) ∧ V ≤ GlobalTheory.LFun.KGL w (n := n)})) :
    ∃ Kw : ∀ w : Plc E, Subgroup (GLw n w), (∀ w, IsOpen (Kw w : Set (GLw n w)) ∧ Kw w ≤ GlobalTheory.LFun.KGL w (n := n)) ∧
      ∀ i ∈ F, Kw i.1 ≤ i.2.1 := by
  induction F using Finset.induction_on with
  | empty =>
    exact ⟨fun w => GlobalTheory.LFun.KGL w (n := n),
      fun w => ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).1, le_rfl⟩, by simp⟩
  | insert i F _ ih =>
    obtain ⟨Kw, h1, h2⟩ := ih
    obtain ⟨v, V, hVo, hVK⟩ := i
    have hle : ∀ w, Function.update Kw v (Kw v ⊓ V) w ≤ Kw w := fun w => by
      by_cases h : w = v
      · subst h
        rw [Function.update_self]
        exact inf_le_left
      · rw [Function.update_of_ne h]
    refine ⟨Function.update Kw v (Kw v ⊓ V), fun w => ?_, fun j hj => ?_⟩
    · refine ⟨?_, (hle w).trans (h1 w).2⟩
      by_cases h : w = v
      · subst h
        rw [Function.update_self]
        exact (h1 w).1.inter hVo
      · rw [Function.update_of_ne h]
        exact (h1 w).1
    · rcases Finset.mem_insert.1 hj with rfl | hj
      · simp only [Function.update_self]
        exact inf_le_right
      · exact (hle j.1).trans (h2 j hj)

end UpperTheory.Gal.CertificateRingHomMap.PNbhd2

theorem UpperTheory.Gal.CertificateRingHomMap.pNbhd2_of :
    UpperTheory.Gal.CertificateRingHomMap.Nbhd2 := by
  intro E _ _ _ n O hO
  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  let p : finU (E := E) (n := n) →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU (E := E) (n := n)).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hfin : ∀ x : UA E n, x ∈ finU (E := E) (n := n) ↔
      finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n) := by
    intro x
    constructor
    · intro hx
      have h1 : GeneralLinearGroup.map (pInf E) (x : GA E n) = 1 := hx
      exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL])
    · intro hx
      change GeneralLinearGroup.map (pInf E) (x : GA E n) = 1
      rw [← hx, pInf_finGL]
  have hc : IsClosed ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) := by
    have e : ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) =
        {x : UA E n | finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n)} :=
      Set.ext hfin
    rw [e]
    exact isClosed_eq (GlobalTheory.DefU.LocAdm.continuous_finGL.comp (continuous_map_pFin.comp continuous_subtype_val))
      continuous_subtype_val
  have hι : Topology.IsClosedEmbedding (fun x : finU (E := E) (n := n) => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hc.isClosedEmbedding_subtypeVal
  have hKc := GlobalTheory.EulerTwRestr.isCompact_Kglob (E := E) (n := n)
  have hKo := GlobalTheory.EulerTwRestr.isOpen_Kglob (E := E) (n := n)
  have hC : IsCompact {u : finU (E := E) (n := n) | p u ∈ GlobalTheory.EulerTw.Kglob E n} :=
    IsCompact.of_isClosed_subset (hι.isCompact_preimage (hKc.image GlobalTheory.DefU.LocAdm.continuous_finGL))
      ((Subgroup.isClosed_of_isOpen _ hKo).preimage hp) fun x hx => ⟨p x, hx, (hfin x).1 x.2⟩
  have hL : ∀ w : Plc E, Continuous fun u : finU (E := E) (n := n) => cLoc w u.1 := fun w =>
    (show Continuous (GeneralLinearGroup.map (n := Fin n) (pLoc E w)) from
      Continuous.units_map _ (Continuous.matrix_map continuous_id
        (show Continuous (pLoc E w) from RestrictedProduct.continuous_eval
          (R := fun w : Plc E => w.adicCompletion E)
          (A := fun w : Plc E => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) w))).comp hp
  let D : (Σ w : Plc E, {V : Subgroup (GLw n w) // IsOpen (V : Set (GLw n w)) ∧ V ≤ GlobalTheory.LFun.KGL w (n := n)}) →
      Set (finU (E := E) (n := n)) := fun i => {u | cLoc i.1 u.1 ∈ i.2.1}
  have hD : ∀ i, IsClosed (D i) := fun i => (Subgroup.isClosed_of_isOpen _ i.2.2.1).preimage (hL i.1)
  have hone : ∀ u : finU (E := E) (n := n), (∀ i, u ∈ D i) → u = 1 := by
    intro u hu
    have h1 : ∀ w : Plc E, cLoc w u.1 = 1 := by
      intro w
      by_contra hne
      obtain ⟨V, hVo, hVK, hV⟩ := UpperTheory.Gal.CertificateRingHomMap.PNbhd2.exists_open_avoid w _ hne
      exact hV (hu ⟨w, V, hVo, hVK⟩)
    have h2 : p u = 1 := GlobalTheory.EulerTwRestr.gl_ext fun w => (h1 w).trans (map_one _).symm
    have h3 : GeneralLinearGroup.map (pInf E) (u.1 : GA E n) = 1 := u.2
    exact Subtype.ext (Subtype.ext (ga_ext (by rw [h3]; simp) (by simpa using (show GeneralLinearGroup.map (pFin E) (u.1 : GA E n) = 1 from h2))))
  have hemp : ({u : finU (E := E) (n := n) | p u ∈ GlobalTheory.EulerTw.Kglob E n} \ (O : Set (finU (E := E) (n := n)))) ∩ ⋂ i, D i = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun u hu => ?_
    have := hone u (Set.mem_iInter.1 hu.2)
    exact hu.1.2 (this ▸ O.one_mem)
  obtain ⟨F, hF⟩ := (hC.diff hO).elim_finite_subfamily_closed D hD (Set.disjoint_iff_inter_eq_empty.mpr hemp)
  obtain ⟨Kw, hK1, hK2⟩ := UpperTheory.Gal.CertificateRingHomMap.PNbhd2.exists_Kw F
  refine ⟨F.image Sigma.fst, Kw, hK1, fun u hu hS => ?_⟩
  by_contra huO
  have hmem : u ∈ ({u : finU (E := E) (n := n) | p u ∈ GlobalTheory.EulerTw.Kglob E n} \ (O : Set (finU (E := E) (n := n)))) ∩ ⋂ i ∈ F, D i :=
    ⟨⟨GlobalTheory.EulerTwRestr.mem_Kglob.2 hu, huO⟩,
      Set.mem_iInter₂.2 fun i hi => hK2 i hi (hS i.1 (Finset.mem_image_of_mem _ hi))⟩
  exact Set.disjoint_left.mp hF hmem.1 hmem.2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.InvTMemSim
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.LFun (KGL IsSatVecGL heckeVec satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

theorem invT_val {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : (invT n R g).val = (g⁻¹).valᵀ := rfl

@[simp] theorem invT_invT' {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : invT n R (invT n R g) = g := by
  apply Units.ext
  rw [invT_val, ← map_inv, invT_val, inv_inv, transpose_transpose]

theorem invT_mem_Sim {A B : Type} [CommRing A] [CommRing B] {σ : A →+* A} {i : B →+* A} {n : ℕ} {p : GL (Fin n) A × Bˣ}
    (h : p ∈ Sim σ i n) : (invT n A p.1, p.2⁻¹) ∈ Sim σ i n := by
  have h1 := mem_Sim.1 h
  have h2 : p.1.valᵀ * p.1.val.map σ = i p.2 • (1 : Matrix (Fin n) (Fin n) A) := by
    have := congrArg transpose h1
    rwa [transpose_mul, transpose_transpose, transpose_smul, transpose_one] at this
  have h3 : i (p.2⁻¹ : Bˣ) * i p.2 = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have h4 : (p.1⁻¹).valᵀ * p.1.valᵀ = 1 := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  have h5 : (p.1⁻¹).val.map σ * p.1.val.map σ = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have h6 : p.1.val.map σ = i p.2 • (p.1⁻¹).valᵀ := by
    rw [← Matrix.one_mul (p.1.val.map σ), ← h4, Matrix.mul_assoc, h2, Matrix.mul_smul, Matrix.mul_one]
  refine mem_Sim.2 ?_
  show (((p.1⁻¹).valᵀ).map σ)ᵀ * (p.1⁻¹).valᵀ = i (p.2⁻¹ : Bˣ) • 1
  rw [transpose_map, transpose_transpose, ← h5, h6, Matrix.mul_smul, smul_smul, h3, one_smul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def th : GUf E n →* GUf E n :=
  (((invT n (Af E)).prodMap invMonoidHom).comp (GUf E n).subtype).codRestrict _ fun g => invT_mem_Sim g.2

def th0 : Gam0 E n →* Gam0 E n :=
  (((invT n E).prodMap invMonoidHom).comp (Gam0 E n).subtype).codRestrict _ fun g =>
    ⟨invT_mem_Sim g.2.1, (Units.posSubgroup ℚ).inv_mem g.2.2⟩

@[simp] theorem sim_th (g : GUf E n) : sim (th g) = (sim g)⁻¹ := rfl

@[simp] theorem comp_th (w : Plc E) (g : GUf E n) : comp w (th g) = invT n _ (comp w g) := GlobalTheory.SplitPts.invT_map _ _

@[simp] theorem th_th (g : GUf E n) : th (th g) = g := Subtype.ext (Prod.ext (invT_invT' _) (inv_inv _))

theorem th_rat (γ : Gam0 E n) : th (rat γ) = rat (th0 γ) :=
  Subtype.ext (Prod.ext (GlobalTheory.SplitPts.invT_map _ _).symm (map_inv (Units.map (algebraMap ℚ AfQ).toMonoidHom) _).symm)

theorem guf_ext {g g' : GUf E n} (h1 : sim g = sim g') (h2 : ∀ w, comp w g = comp w g') : g = g' :=
  Subtype.ext (Prod.ext (Units.ext (GlobalTheory.SplitPts.matAf_ext fun w => congrArg Units.val (h2 w))) h1)

theorem invT_mem_KGL {w : Plc E} {y : GLw n w} (h : y ∈ KGL w (n := n)) : invT n _ y ∈ KGL w (n := n) := by
  obtain ⟨z, rfl⟩ := h
  exact ⟨invT n _ z, GlobalTheory.SplitPts.invT_map _ z⟩

def levT (Kw : ∀ w : Plc E, Subgroup (GLw n w)) : ∀ w : Plc E, Subgroup (GLw n w) := fun w => (Kw w).comap (invT n _)

theorem th_mem_lev {S : Finset (Plc E)} {Kw : ∀ w : Plc E, Subgroup (GLw n w)} {k : GUf E n} :
    th k ∈ lev S Kw ↔ k ∈ lev S (levT Kw) := by
  simp only [mem_lev, sim_th, comp_th, inv_mem_iff, levT, Subgroup.mem_comap]
  refine and_congr_right fun _ => and_congr_right fun _ => forall₃_congr fun w _ _ => ⟨fun h => ?_, invT_mem_KGL⟩
  simpa using invT_mem_KGL h

def ThLoc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
  (∀ (w : Plc E) (hw : IsSplitAt w) (y : GLw n w), th (loc hw y) = loc hw (invT n _ y)) ∧
    (0 < n → ∀ (x : E) (w : Plc E) (z : GUf E n), IsCen x w z → th z = z⁻¹)

end UpperTheory.Gal.CertificateRingHomMap

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PCentralEig2Of
section
open Module

private theorem exists_common_eigenvector_of_commute_of_invariant {E ι : Type} [AddCommGroup E] [Module ℂ E]
    (T : ι → E →ₗ[ℂ] E) (hT : ∀ i j, T i ∘ₗ T j = T j ∘ₗ T i) :
    ∀ n : ℕ, ∀ W : Submodule ℂ E, finrank ℂ W = n → FiniteDimensional ℂ W → W ≠ ⊥ →
      (∀ i, ∀ x ∈ W, T i x ∈ W) → ∃ x ∈ W, x ≠ 0 ∧ ∀ i, ∃ c : ℂ, T i x = c • x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hn hfin hne hW
  by_cases hs : ∀ i, ∃ c : ℂ, ∀ x ∈ W, T i x = c • x
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨x, hx, hx0, fun i => (hs i).imp fun c hc => hc x hx⟩
  · push_neg at hs
    obtain ⟨i, hi⟩ := hs
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((T i).restrict (fun x hx => hW i x hx))
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    set W' : Submodule ℂ E := W ⊓ LinearMap.ker (T i - μ • LinearMap.id) with hW'
    have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ T i x = μ • x := by
      intro x
      simp [hW', sub_eq_zero]
    have hle : W' ≤ W := inf_le_left
    have hlt : W' < W := by
      refine lt_of_le_of_ne hle ?_
      intro heq
      obtain ⟨x, hx, hne'⟩ := hi μ
      exact hne' ((hmem x).1 (by rw [heq]; exact hx)).2
    haveI : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le hle
    have hlt' : finrank ℂ W' < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hlt
    have hne' : W' ≠ ⊥ := by
      intro hbot
      have hv0 : (v : E) ∈ W' := (hmem _).2 ⟨v.2, by
        have := hv.apply_eq_smul
        simpa using congrArg Subtype.val this⟩
      rw [hbot, Submodule.mem_bot] at hv0
      exact hv.2 (Subtype.ext hv0)
    have hW'inv : ∀ j, ∀ x ∈ W', T j x ∈ W' := by
      intro j x hx
      rw [hmem] at hx ⊢
      refine ⟨hW j x hx.1, ?_⟩
      have h1 := LinearMap.congr_fun (hT i j) x
      simp only [LinearMap.comp_apply] at h1
      rw [h1, hx.2, map_smul]
    obtain ⟨x, hx, hx0, hc⟩ := ih _ hlt' W' rfl inferInstance hne' hW'inv
    exact ⟨x, hle hx, hx0, hc⟩

theorem UpperTheory.Gal.CertificateRingHomMap.pCentralEig2_of :
    UpperTheory.Gal.CertificateRingHomMap.CentralEig2 := by
  intro Γ H Z V _ _ _ _ _ ι K ξ ζ hζ M hfin hM hne hinv
  let T : Z → (H → V) →ₗ[ℂ] (H → V) := fun z =>
    { toFun := fun Φ g => Φ (g * ζ z), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hT : ∀ a b, T a ∘ₗ T b = T b ∘ₗ T a := by
    intro a b
    refine LinearMap.ext fun Φ => funext fun g => ?_
    show Φ (g * ζ a * ζ b) = Φ (g * ζ b * ζ a)
    rw [mul_assoc, mul_assoc, hζ a (ζ b)]
  obtain ⟨Φ, hΦM, hΦ0, hc⟩ :=
    exists_common_eigenvector_of_commute_of_invariant T hT _ M rfl hfin hne (fun z Φ hΦ => hinv Φ hΦ z)
  choose c hc using hc
  have hcg : ∀ z g, Φ (g * ζ z) = c z • Φ g := fun z g => congrFun (hc z) g
  obtain ⟨g0, hg0⟩ := Function.ne_iff.mp hΦ0
  have hscal : ∀ a b : ℂ, a • Φ g0 = b • Φ g0 → a = b := fun a b h =>
    smul_left_injective ℂ hg0 h
  have hF : (∀ (γ : Γ) (g : H), Φ (ι γ * g) = ξ γ (Φ g)) ∧ ∀ k ∈ K, ∀ g : H, Φ (g * k) = Φ g :=
    hM hΦM
  have h1 : c 1 = 1 := by
    apply hscal
    rw [← hcg 1 g0, map_one, mul_one, one_smul]
  have hmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    apply hscal
    rw [← hcg (a * b) g0, map_mul, ← mul_assoc, hcg b, hcg a, smul_smul, mul_comm]
  let χ : Z →* ℂ := { toFun := c, map_one' := h1, map_mul' := hmul }
  refine ⟨Φ, hΦM, hΦ0, χ.toHomUnits, ?_, ?_, ?_⟩
  · intro z g
    exact hcg z g
  · intro z hz
    apply Units.ext
    show c z = 1
    apply hscal
    rw [← hcg z g0, hF.2 _ hz g0, one_smul]
  · intro z γ a hzγ hξ
    show c z = a
    apply hscal
    rw [← hcg z g0, ← hξ (Φ g0), ← hF.1 γ g0, ← hzγ, hζ z g0]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExtEig2Of
section
open Module

noncomputable section

namespace UpperTheory.Gal.CertificateRingHomMap

open GlobalTheory.LKDef.HeckeTraceForms

section

variable {Γ H A Z V J : Type} [Group Γ] [Group H] [Group A] [Group Z] [AddCommGroup V] [Module ℂ V]

private theorem rop_add (r : H →₀ ℂ) (Φ Ψ : H → V) : rop r (Φ + Ψ) = rop r Φ + rop r Ψ := by
  funext g
  simp only [rop, Pi.add_apply, smul_add, Finsupp.sum_add]

private theorem rop_smul (r : H →₀ ℂ) (a : ℂ) (Φ : H → V) : rop r (a • Φ) = a • rop r Φ := by
  funext g
  simp only [rop, Pi.smul_apply, Finsupp.smul_sum, smul_smul, mul_comm]

private def eigForms (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (r : J → H →₀ ℂ) (θ : J → ℂ) :
    Submodule ℂ (H → V) where
  carrier := {Φ | Φ ∈ forms ι K ξ ∧ ∀ j, rop (r j) Φ = θ j • Φ}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨add_mem ha hb, fun j => by rw [rop_add, ha', hb', smul_add]⟩
  zero_mem' := ⟨zero_mem _, fun j => by
    have := rop_smul (r j) (0 : ℂ) (0 : H → V)
    simpa using this⟩
  smul_mem' := by
    rintro a b ⟨hb, hb'⟩
    exact ⟨Submodule.smul_mem _ a hb, fun j => by rw [rop_smul, hb', smul_comm]⟩

end

theorem pExtEig2_of : ExtZero → CentralEig2 → ExtEig2 := by
  intro hZ hC
  unfold ExtEig2
  intro Γ H A Z V _ _ _ _ _ _ ι K ξ c ζ hcen hs φ hφ hφne J r θ hsupp hforms heig
  obtain ⟨s, hs⟩ := hs
  obtain ⟨u₀, hu₀, hφu₀⟩ := hφne
  have memF : ∀ Ψ : H → V, Ψ ∈ forms ι K ξ ↔
      ((∀ γ g, Ψ (ι γ * g) = ξ γ (Ψ g)) ∧ ∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) := fun Ψ => Iff.rfl
  obtain ⟨Φ, hΦ, hext, hsup⟩ := hZ Γ H A V ι K ξ c φ hφ
  obtain ⟨hΦ1, hΦ2⟩ := (memF Φ).1 hΦ
  have hΦne : Φ ≠ 0 := by
    intro h
    apply hφu₀
    rw [← hext u₀ hu₀, h]
    rfl
  have hΦeig : ∀ j, rop (r j) Φ = θ j • Φ := by
    intro j
    have hu : ∀ u, c u = 1 → rop (r j) Φ u = θ j • Φ u := by
      intro u hu
      rw [hext u hu, ← heig j u hu]
      simp only [rop, Finsupp.sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [hext (u * v) (by rw [map_mul, hu, hsupp j v hv, one_mul])]
    obtain ⟨hf1, hf2⟩ := (memF _).1 (hforms j Φ hΦ)
    funext g
    by_cases hg : ∃ γ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ * u * k
    · obtain ⟨γ, u, k, hu', hk, rfl⟩ := hg
      rw [Pi.smul_apply, mul_assoc, hf1 γ (u * k), hf2 k hk u, hΦ1 γ (u * k), hΦ2 k hk u,
        hu u hu', map_smul]
    · have h0 : Φ g = 0 := by
        by_contra h
        exact hg (hsup g h)
      rw [Pi.smul_apply, h0, smul_zero]
      simp only [rop, Finsupp.sum]
      apply Finset.sum_eq_zero
      intro v hv
      have hcv := hsupp j v hv
      have hz : Φ (g * v) = 0 := by
        by_contra h
        obtain ⟨γ, u, k, hu', hk, he⟩ := hsup _ h
        apply hg
        refine ⟨γ, u * (k * v⁻¹ * k⁻¹), k, ?_, hk, ?_⟩
        · simp [map_mul, map_inv, hu', hcv]
        · calc g = g * v * v⁻¹ := by group
            _ = ι γ * u * k * v⁻¹ := by rw [he]
            _ = ι γ * (u * (k * v⁻¹ * k⁻¹)) * k := by group
      rw [hz, smul_zero]
  have trForms : ∀ Ψ ∈ forms ι K ξ, ∀ z, (fun g => Ψ (g * ζ z)) ∈ forms ι K ξ := by
    intro Ψ hΨ z
    obtain ⟨h1, h2⟩ := (memF Ψ).1 hΨ
    refine (memF _).2 ⟨fun γ g => ?_, fun k hk g => ?_⟩
    · show Ψ (ι γ * g * ζ z) = ξ γ (Ψ (g * ζ z))
      rw [mul_assoc, h1]
    · show Ψ (g * k * ζ z) = Ψ (g * ζ z)
      rw [mul_assoc, ← hcen z k, ← mul_assoc, h2 k hk]
  have trRop : ∀ (Ψ : H → V) j z,
      rop (r j) (fun g => Ψ (g * ζ z)) = fun g => rop (r j) Ψ (g * ζ z) := by
    intro Ψ j z
    funext g
    simp only [rop, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [mul_assoc g (ζ z), hcen z u, mul_assoc]
  have key : ∀ z, ∃ t ∈ s, ∃ a : ℂ, (fun g => Φ (g * ζ z)) = a • fun g => Φ (g * ζ t) := by
    intro z
    obtain ⟨t, ht, z₀, z₁, rfl, hz₀, γ, a, hz₁, ha⟩ := hs z
    refine ⟨t, ht, a, ?_⟩
    funext g
    show Φ (g * ζ (t * z₀ * z₁)) = a • Φ (g * ζ t)
    rw [map_mul, map_mul, ← mul_assoc, ← mul_assoc, ← hcen z₁, hz₁, hΦ1, ha, hΦ2 _ hz₀]
  let M : Submodule ℂ (H → V) := Submodule.span ℂ ((fun t g => Φ (g * ζ t)) '' (s : Set Z))
  have hfin : FiniteDimensional ℂ M :=
    FiniteDimensional.span_of_finite ℂ ((s.finite_toSet).image _)
  have trM : ∀ z, (fun g => Φ (g * ζ z)) ∈ M := by
    intro z
    obtain ⟨t, ht, a, he⟩ := key z
    rw [he]
    exact M.smul_mem a (Submodule.subset_span ⟨t, ht, rfl⟩)
  have hΦM : Φ ∈ M := by
    have h := trM 1
    simp only [map_one, mul_one] at h
    exact h
  have hle : M ≤ eigForms ι K ξ r θ := by
    apply Submodule.span_le.2
    rintro _ ⟨t, _, rfl⟩
    show (fun g => Φ (g * ζ t)) ∈ forms ι K ξ ∧
      ∀ j, rop (r j) (fun g => Φ (g * ζ t)) = θ j • (fun g => Φ (g * ζ t))
    refine ⟨trForms Φ hΦ t, fun j => ?_⟩
    rw [trRop, hΦeig j]
    rfl
  have hE : ∀ Ψ ∈ M, Ψ ∈ forms ι K ξ ∧ ∀ j, rop (r j) Ψ = θ j • Ψ := fun Ψ h => hle h
  have hne : M ≠ ⊥ := by
    intro h
    apply hΦne
    have h' := hΦM
    rw [h] at h'
    exact (Submodule.mem_bot ℂ).1 h'
  have hclos : ∀ Ψ ∈ M, ∀ z, (fun g => Ψ (g * ζ z)) ∈ M := by
    intro Ψ hΨ z
    have hL : M ≤ M.comap (LinearMap.funLeft ℂ V (fun g : H => g * ζ z)) := by
      apply Submodule.span_le.2
      rintro _ ⟨t, _, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have h := trM (z * t)
      simp only [map_mul, ← mul_assoc] at h
      exact h
    exact hL hΨ
  obtain ⟨Ψ, hΨM, hΨne, ψ, hψ⟩ :=
    hC Γ H Z V ι K ξ ζ hcen M hfin (fun Ψ h => (hE Ψ h).1) hne hclos
  exact ⟨Ψ, (hE Ψ hΨM).1, hΨne, (hE Ψ hΨM).2, ψ, hψ⟩

end UpperTheory.Gal.CertificateRingHomMap

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.POfUBij
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pOfUBij_of :
    UpperTheory.Gal.CertificateRingHomMap.OfUBij := by
  intro E _ _ _ n
  refine ⟨fun u v h => ?_, fun g hg => ?_⟩
  · have h1 : GeneralLinearGroup.map (pFin E) u.1.1 = GeneralLinearGroup.map (pFin E) v.1.1 :=
      congrArg (fun x : GUf E n => mat x) h
    have h2 := congrArg (finGL E n) h1
    rw [GlobalTheory.DefU.ClassFin.finGL_pFin, GlobalTheory.DefU.ClassFin.finGL_pFin] at h2
    exact Subtype.ext (Subtype.ext h2)
  · have hs : g.1.2 = 1 := hg
    have h : Formalism.UG.cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (mat g).val * (mat g).val = 1 :=
      (mem_Sim.1 g.2).trans (by rw [hs]; simp)
    refine ⟨⟨⟨finGL E n (mat g), GlobalTheory.DefU.ClassFin.finGL_mem_UA _ h⟩, pInf_finGL _⟩, ?_⟩
    exact Subtype.ext (Prod.ext (pFin_finGL _) hs.symm)
end

