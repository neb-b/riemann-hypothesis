module

public import Formalism.LocalToGlobal.Columns.Bundle0012
public import Formalism.LocalToGlobal.Columns.Bundle0015
public import Formalism.LocalToGlobal.Columns.Bundle0014
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.Bundle0001
public import Formalism.LocalToGlobal.HermitianForms.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.HxMemMap
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : ColRec}

theorem hx_hform (i : ℕ) (hi : i ≤ D.R.m) (x y : (D.sp.X i).V) :
    (D.sp.X i).hT x y = hform (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi) (CF.crdN D i hi x) (CF.crdN D i hi y) := by
  rw [Formalism.L2.Herm.hT_crd D.sp.cm (D.sp.X i) x y]
  unfold hform
  rw [← (finCongr (CF.rankN D i hi)).symm.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← (finCongr (CF.rankN D i hi)).symm.sum_comp]
  exact Finset.sum_congr rfl fun b _ => rfl

variable (u : D.what₂.Word)

theorem hx_clsCrd (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    CF.clsCrd D u i hi c = (D.clsLat u i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) := rfl

theorem hx_Ld_eq (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    CF.Ld D u i hi c = (CH.Ld D u i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) := by
  have key : (((CH.Ld D u i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) :
        Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) =
      dualSet (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi) (CF.clsCrd D u i hi c) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩ s ⟨y, hy, rfl⟩
      have := (Formalism.L2.Herm.mem_dual (D.sp.X i) (D.clsLat u i c) x).1 hx y hy
      rw [hx_hform i hi] at this
      exact this
    · intro ht
      refine ⟨(CF.crdN D i hi).symm t, ?_, (CF.crdN D i hi).apply_symm_apply t⟩
      refine (Formalism.L2.Herm.mem_dual (D.sp.X i) (D.clsLat u i c) _).2 fun y hy => ?_
      rw [hx_hform i hi, LinearEquiv.apply_symm_apply]
      exact ht (CF.crdN D i hi y) ⟨y, hy, rfl⟩
  show Submodule.span (𝓞 D.host.E) (dualSet _ _ _) = _
  rw [← key, Submodule.span_eq]

theorem hx_mem_map {i : ℕ} (hi : i ≤ D.R.m) (M : Submodule (𝓞 D.host.E) (D.sp.X i).V) (x : (D.sp.X i).V) :
    CF.crdN D i hi x ∈ M.map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) ↔ x ∈ M := by
  constructor
  · rintro ⟨y, hy, e⟩
    have : y = x := (CF.crdN D i hi).injective e
    exact this ▸ hy
  · exact fun h => ⟨x, h, rfl⟩

theorem hx_mem_Ld (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) (x : (D.sp.X i).V) :
    CF.crdN D i hi x ∈ CF.Ld D u i hi c ↔ x ∈ CH.Ld D u i c := by
  rw [hx_Ld_eq, hx_mem_map]

theorem hx_smul_Ld (I : Ideal (𝓞 D.host.E)) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    I • CF.Ld D u i hi c = (I • CH.Ld D u i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) := by
  rw [hx_Ld_eq, Submodule.map_smul'']

theorem hx_Lk_eq (I : Ideal (𝓞 D.host.E)) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    CF.clsCrd D u i hi c ⊔ I • CF.Ld D u i hi c = (CH.Lk D u I i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) := by
  rw [hx_smul_Ld, hx_clsCrd, ← Submodule.map_sup]

variable {u} (A : CF.AtTTied u) (P : ∀ i hi, CF.LvTied u A i hi)

theorem hx_mem_Lk (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (x : (D.sp.X i).V) :
    CF.crdN D i hi x ∈ CF.Lk A i hi v c ↔ x ∈ CH.Lk D u (A.Pv v) i c := by
  show CF.crdN D i hi x ∈ CF.clsCrd D u i hi c ⊔ A.Pv v • CF.Ld D u i hi c ↔ _
  rw [hx_Lk_eq, hx_mem_map]

def hxLd (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) : ↥(CH.Ld D u i c) →+ ↥(CF.Ld D u i hi c) where
  toFun z := ⟨CF.crdN D i hi z.1, (hx_mem_Ld u i hi c z.1).2 z.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

def hxLk (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    ↥(CH.Lk D u (A.Pv v) i c) →+ ↥(CF.Lk A i hi v c) where
  toFun z := ⟨CF.crdN D i hi z.1, (hx_mem_Lk A i hi v c z.1).2 z.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)


open Classical in
def hxPr (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) : ↥(CH.Ld D u i c) →+ (D.fm u).lv i v c :=
  if hi : i ≤ D.R.m then ((P i hi).pr v c).comp (hxLd i hi c) else 0


open Classical in
def hxPrk (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) : ↥(CH.Lk D u (A.Pv v) i c) →+ (D.fm u).lk i v c :=
  if hi : i ≤ D.R.m then ((P i hi).prk v c).comp (hxLk A i hi v c) else 0

theorem hxPr_eq (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Ld D u i c)) :
    hxPr A P i v c z = (P i hi).pr v c (hxLd i hi c z) := by
  unfold hxPr; rw [dite_eq_left hi]; rfl

theorem hxPrk_eq (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Lk D u (A.Pv v) i c)) :
    hxPrk A P i v c z = (P i hi).prk v c (hxLk A i hi v c z) := by
  unfold hxPrk; rw [dite_eq_left hi]; rfl

theorem hxPr_surj (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Function.Surjective (hxPr A P i v c) := by
  intro q
  obtain ⟨z, rfl⟩ := (P i hi).pr_surj v c q
  refine ⟨⟨(CF.crdN D i hi).symm z.1, (hx_mem_Ld u i hi c _).1 (by rw [LinearEquiv.apply_symm_apply]; exact z.2)⟩, ?_⟩
  rw [hxPr_eq A P i hi]
  congr 1
  exact Subtype.ext ((CF.crdN D i hi).apply_symm_apply z.1)

theorem hxPr_smul (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (r : 𝓞 D.host.E) (z : ↥(CH.Ld D u i c)) :
    hxPr A P i v c (r • z) = A.res v r • hxPr A P i v c z := by
  by_cases hi : i ≤ D.R.m
  · rw [hxPr_eq A P i hi, hxPr_eq A P i hi, ← (P i hi).pr_smul]
    congr 1
    exact Subtype.ext (((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars
      (𝓞 D.host.E)).map_smul r z.1)
  · unfold hxPr; rw [dite_eq_right hi]; simp

theorem hxPr_ker (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Ld D u i c)) :
    hxPr A P i v c z = 0 ↔ z.1 ∈ A.Pv v • CH.Ld D u i c := by
  rw [hxPr_eq A P i hi, (P i hi).pr_ker, hx_smul_Ld]
  exact hx_mem_map hi _ z.1

theorem hx_fv_ker (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Ld D u i c)) :
    (D.fm u).fv i v c (hxPr A P i v c z) = 0 ↔ z.1 ∈ CH.Lk D u (A.Pv v) i c := by
  rw [hxPr_eq A P i hi, (P i hi).fv_ker]
  exact hx_mem_Lk A i hi v c z.1

theorem hxPrk_surj (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Function.Surjective (hxPrk A P i v c) := by
  intro q
  obtain ⟨z, rfl⟩ := (P i hi).prk_surj v c q
  refine ⟨⟨(CF.crdN D i hi).symm z.1, (hx_mem_Lk A i hi v c _).1 (by rw [LinearEquiv.apply_symm_apply]; exact z.2)⟩, ?_⟩
  rw [hxPrk_eq A P i hi]
  congr 1
  exact Subtype.ext ((CF.crdN D i hi).apply_symm_apply z.1)

theorem hxPrk_smul (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (r : 𝓞 D.host.E) (z : ↥(CH.Lk D u (A.Pv v) i c)) :
    hxPrk A P i v c (r • z) = A.res v r • hxPrk A P i v c z := by
  by_cases hi : i ≤ D.R.m
  · rw [hxPrk_eq A P i hi, hxPrk_eq A P i hi, ← (P i hi).prk_smul]
    congr 1
    exact Subtype.ext (((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars
      (𝓞 D.host.E)).map_smul r z.1)
  · unfold hxPrk; rw [dite_eq_right hi]
    change (0 : (D.fm u).lk i v c) = A.res v r • 0
    exact (smul_zero _).symm

theorem hxPrk_ker (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Lk D u (A.Pv v) i c)) :
    hxPrk A P i v c z = 0 ↔ z.1 ∈ A.Pv v • CH.Lk D u (A.Pv v) i c := by
  rw [hxPrk_eq A P i hi, (P i hi).prk_ker]
  show CF.crdN D i hi z.1 ∈ A.Pv v • (CF.clsCrd D u i hi c ⊔ A.Pv v • CF.Ld D u i hi c) ↔ _
  rw [hx_Lk_eq, ← Submodule.map_smul'']
  exact hx_mem_map hi _ z.1

theorem hx_te (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Ld D u i c))
    (hz : (D.fm u).fv i v c (hxPr A P i v c z) = 1)
    (h : ((D.mem u).A.T : D.host.E) • z.1 ∈ CH.Lk D u (A.Pv v) i c) :
    hxPrk A P i v c ⟨_, h⟩ = (D.fm u).te i v c := by
  rw [hxPr_eq A P i hi] at hz
  have e : CF.crdN D i hi (((D.mem u).A.T : D.host.E) • z.1) = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (hxLd i hi c z).1 := by
    rw [map_smul]
    show _ = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • CF.crdN D i hi z.1
    rw [Algebra.smul_def' , map_natCast] <;> rfl
  have h' : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (hxLd i hi c z).1 ∈ CF.Lk A i hi v c := by
    rw [← e]; exact (hx_mem_Lk A i hi v c _).2 h
  rw [hxPrk_eq A P i hi, ← (P i hi).te v c (hxLd i hi c z) hz h']
  congr 1
  exact Subtype.ext e

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedGlLoc
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV
open Formalism.L2.Forms (kv redM)

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)

def gloPhi : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F := (RingHom.fst _ _).comp spl.toRingHom

variable (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a))

include halg in
theorem gloPhi_int (x : E ⊗[F] v.adicCompletion F) (hx : x ∈ Formalism.BasicNotions.intV E v) :
    gloPhi v spl x ∈ v.adicCompletionIntegers F :=
  ((Formalism.L2.G.split_integral_completion F E v spl halg x).1 hx).1

def gloRho : Formalism.L2.Herm.intAf F E →+* kv F v :=
  (IsLocalRing.residue (v.adicCompletionIntegers F)).comp
    ((((gloPhi v spl).comp (prV (E := E) v)).comp (Formalism.L2.Herm.intAf F E).subtype).codRestrict (v.adicCompletionIntegers F)
      fun s => gloPhi_int v spl halg _ (afsplit_prV_int v _ s.2))

theorem gloRho_apply (s : Formalism.L2.Herm.intAf F E) :
    gloRho v spl halg s = IsLocalRing.residue (v.adicCompletionIntegers F)
      ⟨gloPhi v spl (prV (E := E) v (s : E ⊗[F] Formalism.L2.Herm.Af F)), gloPhi_int v spl halg _ (afsplit_prV_int v _ s.2)⟩ := rfl

variable (w : Pl E) (hw : ∀ a ∈ w.asIdeal, gloRho v spl halg (oToS F E a) = 0)

def gloK : kP w →+* kv F v := Ideal.Quotient.lift w.asIdeal ((gloRho v spl halg).comp (oToS F E)) hw

theorem gloRho_eq (s : Formalism.L2.Herm.intAf F E) : gloRho v spl halg s = gloK v spl halg w hw (resS F w s) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (resS F w s)
  have h1 : resS F w (s - oToS F E a) = 0 := by rw [map_sub, resS_oToS, ha, sub_self]
  rw [resS_eq_zero_iff] at h1
  have h2 : idS F w.asIdeal ≤ RingHom.ker (gloRho v spl halg) := by
    unfold idS
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    exact hw b hb
  have h3 : gloRho v spl halg (s - oToS F E a) = 0 := h2 h1
  rw [map_sub, sub_eq_zero] at h3
  rw [h3, ← ha]
  rfl

theorem glo_res_zero (x : v.adicCompletionIntegers F) (h : Valued.v (x : v.adicCompletion F) < 1) :
    IsLocalRing.residue (v.adicCompletionIntegers F) x = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, rfl⟩
  have h1 : ((u : v.adicCompletionIntegers F) : v.adicCompletion F) * ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) :
      v.adicCompletionIntegers F) = 1 := by
    have := congrArg (Subtype.val) u.mul_inv
    exact this
  have h2 := congrArg Valued.v h1
  rw [map_mul, map_one] at h2
  have h3 : Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (Subtype.mem _)
  have h4 := mul_le_mul' h.le h3
  rw [h2, one_mul] at h4
  have h5 : Valued.v ((u : v.adicCompletionIntegers F) : v.adicCompletion F) *
      Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) ≤
      Valued.v ((u : v.adicCompletionIntegers F) : v.adicCompletion F) := mul_le_of_le_one_right' h3
  rw [h2] at h5
  exact absurd h (not_lt.2 h5)

theorem glo_algMap_int (r : 𝓞 F) : algebraMap (𝓞 F) (v.adicCompletion F) r ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, csApprox_val_int]
  exact HeightOneSpectrum.intValuation_le_one v r

theorem glo_res_surj (z : kv F v) : ∃ r : 𝓞 F,
    IsLocalRing.residue (v.adicCompletionIntegers F) ⟨algebraMap (𝓞 F) (v.adicCompletion F) r, glo_algMap_int v r⟩ = z := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨D, hDv, hD⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  obtain ⟨r, y, hy, e⟩ := integral_adele_approximation_holds F D hD (afsplitI v (x : v.adicCompletion F)) (afsplitI_mem_intAd v _ x.2)
  refine ⟨r, ?_⟩
  have ev : (x : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) r + algebraMap (𝓞 F) (v.adicCompletion F) D * y v := by
    have := congrArg (fun z : Formalism.L2.Herm.Af F => z v) e
    rw [afsplitI_self] at this
    exact this
  have hDval : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1 := by
    rw [csApprox_val_int]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v D).2 hDv
  have hyv : Valued.v (y v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hy v)
  have hlt : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D * y v) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hyv) hDval
  have hmem : algebraMap (𝓞 F) (v.adicCompletion F) D * y v ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hlt.le
  have hx : x = ⟨algebraMap (𝓞 F) (v.adicCompletion F) r, glo_algMap_int v r⟩ + ⟨_, hmem⟩ := Subtype.ext ev
  rw [hx, map_add (f := _), glo_res_zero v ⟨_, hmem⟩ hlt, add_zero]

theorem gloRho_algMap (r : 𝓞 F) : gloRho v spl halg (oToS F E (algebraMap (𝓞 F) (𝓞 E) r)) =
    IsLocalRing.residue (v.adicCompletionIntegers F) ⟨algebraMap (𝓞 F) (v.adicCompletion F) r, glo_algMap_int v r⟩ := by
  rw [gloRho_apply]
  congr 1
  apply Subtype.ext
  show gloPhi v spl (prV (E := E) v (inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r)))) = _
  rw [afsplit_prV_inclE]
  have h1 : inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r)) =
      (1 : E) ⊗ₜ[F] (algebraMap (𝓞 F) (v.adicCompletion F) r) := by
    show (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r)) ⊗ₜ[F] (1 : v.adicCompletion F) = _
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, IsScalarTower.algebraMap_apply (𝓞 F) F E, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_apply]
  rw [h1]
  show (spl _).1 = _
  rw [halg]

theorem gloK_bijective : Function.Bijective (gloK v spl halg w hw) := by
  constructor
  · haveI : w.asIdeal.IsMaximal := w.isMaximal
    letI := Ideal.Quotient.field w.asIdeal
    exact RingHom.injective (gloK v spl halg w hw)
  · intro z
    obtain ⟨r, rfl⟩ := glo_res_surj v z
    refine ⟨Ideal.Quotient.mk w.asIdeal (algebraMap (𝓞 F) (𝓞 E) r), ?_⟩
    rw [← gloRho_algMap v spl halg r]
    rfl

def gloE : kP w ≃+* kv F v := RingEquiv.ofBijective (gloK v spl halg w hw) (gloK_bijective v spl halg w hw)

theorem gloE_resS (s : Formalism.L2.Herm.intAf F E) : gloE v spl halg w hw (resS F w s) = gloRho v spl halg s :=
  (gloRho_eq v spl halg w hw s).symm

end Loc

end Formalism.L2.Col
end
end

