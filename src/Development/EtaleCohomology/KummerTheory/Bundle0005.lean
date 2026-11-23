module

public import Development.EtaleCohomology.KummerTheory.Bundle0002
public import Development.EtaleCohomology.KummerTheory.FinalTheorems

@[expose] public section

-- bundled from Development.EtaleCohomology.KummerTheory.AdicAlgPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.KummerTheory

section Alg
variable (l : ℕ) [Fact l.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[l] M]

theorem adic_decomp [Module.Finite ℤ_[l] M] : ∃ (r : ℕ) (c : Fin r → M) (e : ℕ), 0 < e ∧
    LinearIndependent ℤ_[l] c ∧ ∀ x : M, ∃ (a : Fin r → ℤ_[l]) (τ : M), x = ∑ s, a s • c s + τ ∧ e • τ = 0 := by
  classical
  set T := Submodule.torsion ℤ_[l] M
  have hTfin : Module.Finite ℤ_[l] T := inferInstance
  obtain ⟨a, ha, ha0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors (Submodule.torsion_isTorsion (R := ℤ_[l]) (M := M))
  have hane : a ≠ 0 := nonZeroDivisors.ne_zero ha0
  have hkill : ∀ τ ∈ T, (l ^ a.valuation : ℕ) • τ = 0 := by
    intro τ hτ
    have h1 : a • (⟨τ, hτ⟩ : T) = 0 := Submodule.mem_annihilator.mp ha _ Submodule.mem_top
    have h2 : a • τ = 0 := congrArg Subtype.val h1
    rw [PadicInt.unitCoeff_spec hane, mul_smul] at h2
    have h3 := congrArg (fun v => (((PadicInt.unitCoeff hane)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • v) h2
    simp only [smul_zero, smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at h3
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]
    push_cast
    exact h3
  set Q := M ⧸ T
  let b := Module.finBasis ℤ_[l] Q
  let c : Fin (Module.finrank ℤ_[l] Q) → M := fun s => (Submodule.Quotient.mk_surjective T (b s)).choose
  have hc : ∀ s, T.mkQ (c s) = b s := fun s => (Submodule.Quotient.mk_surjective T (b s)).choose_spec
  have hcomp : T.mkQ ∘ c = b := funext hc
  refine ⟨_, c, l ^ a.valuation, pow_pos (Fact.out : l.Prime).pos _, ?_, ?_⟩
  · exact LinearIndependent.of_comp T.mkQ (hcomp ▸ b.linearIndependent)
  · intro x
    refine ⟨b.repr (T.mkQ x), x - ∑ s, b.repr (T.mkQ x) s • c s, by abel, hkill _ ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
    simp only [map_smul, hc]
    rw [b.sum_repr, sub_self]

theorem adic_qbasis {r : ℕ} (c : Fin r → M) (e : ℕ) (he : 0 < e) (hli : LinearIndependent ℤ_[l] c)
    (hdec : ∀ x : M, ∃ (a : Fin r → ℤ_[l]) (τ : M), x = ∑ s, a s • c s + τ ∧ e • τ = 0) :
    LinearIndependent ℚ_[l] (fun s => ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c s : ℚ_[l] ⊗[ℤ_[l]] M)) ∧
    Submodule.span ℚ_[l] (Set.range fun s => ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c s : ℚ_[l] ⊗[ℤ_[l]] M)) = ⊤ := by
  let f := TensorProduct.mk ℤ_[l] ℚ_[l] M 1
  refine ⟨hli.of_isLocalizedModule ℚ_[l] (nonZeroDivisors ℤ_[l]) f, ?_⟩
  have htop := span_eq_top_of_isLocalizedModule ℚ_[l] (nonZeroDivisors ℤ_[l]) f (v := Set.univ) Submodule.span_univ
  refine top_unique (htop ▸ Submodule.span_le.mpr ?_)
  rintro _ ⟨x, -, rfl⟩
  obtain ⟨a, τ, rfl, hτ⟩ := hdec x
  have hfτ : f τ = 0 := by
    have h1 : (e : ℚ_[l]) • f τ = 0 := by rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, hτ, map_zero]
    exact (smul_eq_zero.mp h1).resolve_left (Nat.cast_ne_zero.mpr he.ne')
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), hfτ, add_zero, map_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [map_smul]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

end Alg

def levH (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) (k : ℕ) : Hl l E n i →+ Ht (l ^ k) E n i where
  toFun x := lev l x k
  map_zero' := rfl
  map_add' _ _ := rfl

theorem lev_comb (l : ℕ) [Fact l.Prime] {E : Spc} {n i : ℤ} {r : ℕ} (c : Fin r → Hl l E n i) (a : Fin r → ℤ_[l]) (k : ℕ) :
    lev l (∑ s, a s • c s) k = comb (l ^ k) (fun s => lev l (c s) k) (fun s => PadicInt.toZModPow k (a s)) := by
  change levH l E n i k _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  rfl

theorem AdicAlg_of : AdicAlg := by
  intro l _ E n i hfin hker M hM hcok
  obtain ⟨r, c, e, he, hli, hdec⟩ := adic_decomp l (M := Hl l E n i)
  refine ⟨r, c, e * M, Nat.mul_pos he hM, adic_qbasis l c e he hli hdec, fun k => ⟨?_, ?_⟩⟩
  · intro t ht
    have : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    let a : Fin r → ℤ_[l] := fun s => ((t s).val : ℤ_[l])
    have hat : (fun s => PadicInt.toZModPow k (a s)) = t := funext fun s => by simp [a]
    have hx : lev l (∑ s, a s • c s) k = 0 := by rw [lev_comb, hat]; exact ht
    obtain ⟨y, hy⟩ := hker k _ hx
    obtain ⟨b, τ, rfl, hτ⟩ := hdec y
    have heq : ∑ s, ((e : ℤ_[l]) * a s - (e : ℤ_[l]) * (l : ℤ_[l]) ^ k * b s) • c s = 0 := by
      have h1 := congrArg (fun v => (e : ℤ_[l]) • v) hy
      simp only [smul_add, Finset.smul_sum, smul_smul] at h1
      have h2 : (e : ℤ_[l]) • (l : ℤ_[l]) ^ k • τ = 0 := by
        rw [smul_comm, Nat.cast_smul_eq_nsmul, hτ, smul_zero]
      rw [smul_smul] at h2
      rw [h2, add_zero] at h1
      simp only [sub_smul, Finset.sum_sub_distrib, h1, mul_assoc, sub_self]
    have hs := Fintype.linearIndependent_iff.mp hli _ heq
    have ht0 : t = 0 := by
      funext s
      have h3 : a s = (l : ℤ_[l]) ^ k * b s := by
        have h4 := hs s
        rw [sub_eq_zero, mul_assoc] at h4
        exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr he.ne') h4
      rw [← congrFun hat s]
      simp only [h3, map_mul, map_pow, map_natCast, Pi.zero_apply]
      rw [show ((l : ZMod (l ^ k)) ^ k) = ((l ^ k : ℕ) : ZMod (l ^ k)) by push_cast; rfl, ZMod.natCast_self, zero_mul]
    rw [ht0, smul_zero]
  · intro z
    obtain ⟨x, hx⟩ := hcok k z
    obtain ⟨a, τ, rfl, hτ⟩ := hdec x
    refine ⟨fun s => PadicInt.toZModPow k ((e : ℤ_[l]) * a s), ?_⟩
    rw [← lev_comb, mul_smul, ← hx]
    have key : ∀ w, lev l (e • w) k = e • lev l w k := fun w => map_nsmul (levH l E n i k) e w
    rw [← key, smul_add, hτ, add_zero, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_smul, Nat.cast_smul_eq_nsmul]

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.AdicLimPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def AdicKer : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (i : ℤ), (∀ b, BockData l b E i) →
  (∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) → ∀ (n : ℤ) (k : ℕ) (x : Hl l E n i), lev l x k = 0 →
    ∃ y : Hl l E n i, x = ((l : ℤ_[l]) ^ k) • y

def AdicFin : Prop := ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ), (∀ k : ℕ, Finite (Ht (l ^ k) E n i)) →
  (∀ (k : ℕ) (x : Hl l E n i), lev l x k = 0 → ∃ y : Hl l E n i, x = ((l : ℤ_[l]) ^ k) • y) →
    Module.Finite ℤ_[l] (Hl l E n i)

def AdicCok : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (i : ℤ), (∀ b, BockData l b E i) →
  (∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) → ∀ n : ℤ, Module.Finite ℤ_[l] (Hl l E (n + 1) i) →
    ∃ M : ℕ, 0 < M ∧ ∀ (k : ℕ) (z : Ht (l ^ k) E n i), ∃ x : Hl l E n i, lev l x k = M • z

theorem AdicLim_of (hK : AdicKer) (hF : AdicFin) (hC : AdicCok) : AdicLim := by
  intro hA l _ E i hB hFin n
  have hker : ∀ m : ℤ, ∀ (k : ℕ) (x : Hl l E m i), lev l x k = 0 → ∃ y : Hl l E m i, x = ((l : ℤ_[l]) ^ k) • y :=
    fun m => hK hA l E i hB hFin m
  have hfin : ∀ m : ℤ, Module.Finite ℤ_[l] (Hl l E m i) := fun m => hF l E m i (fun k => hFin k m) (hker m)
  exact ⟨hfin n, hker n, hC hA l E i hB hFin n (hfin (n + 1))⟩

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.AffRingPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.KummerTheory.AffRingPf

variable {X : Scheme.{0}} [IsAffine X] {R : CommRingCat.{0}} (p : X ⟶ Spec R)

def phi : R ⟶ Γ(X, ⊤) := Spec.preimage (X.isoSpec.inv ≫ p)

def Tf : Under R ⥤ CommRingCat.{0} := Under.pushout (phi p) ⋙ Under.forget _

theorem isPb (A : Under R) :
    IsPullback (Spec.map (pushout.inr A.hom (phi p)) ≫ X.isoSpec.inv) (Spec.map (pushout.inl A.hom (phi p)))
      p (Spec.map A.hom) := by
  have h := (isPullback_SpecMap_pushout A.hom (phi p)).flip
  refine IsPullback.of_iso h (Iso.refl _) X.isoSpec.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp [phi]
  · simp

def eIso (A : Under R) : Spec (pushout A.hom (phi p)) ≅ pullback p (Spec.map A.hom) := (isPb p A).isoPullback

theorem eIso_fst (A : Under R) : (eIso p A).hom ≫ pullback.fst _ _ =
    Spec.map (pushout.inr A.hom (phi p)) ≫ X.isoSpec.inv :=
  (isPb p A).isoPullback_hom_fst

theorem eIso_snd (A : Under R) : (eIso p A).hom ≫ pullback.snd _ _ =
    Spec.map (pushout.inl A.hom (phi p)) :=
  (isPb p A).isoPullback_hom_snd

def tmap {A B : Under R} (h : A ⟶ B) : pushout A.hom (phi p) ⟶ pushout B.hom (phi p) :=
  pushout.desc (h.right ≫ pushout.inl B.hom (phi p)) (pushout.inr B.hom (phi p))
    (by rw [← Category.assoc, Under.w h, pushout.condition])

theorem nat {A B : Under R} (h : A ⟶ B) :
    (eIso p B).hom ≫ bcMap p A.hom B.hom h.right (Under.w h) = Spec.map (tmap p h) ≫ (eIso p A).hom := by
  have e1 : pushout.inr A.hom (phi p) ≫ tmap p h = pushout.inr B.hom (phi p) := pushout.inr_desc _ _ _
  have e2 : pushout.inl A.hom (phi p) ≫ tmap p h = h.right ≫ pushout.inl B.hom (phi p) := pushout.inl_desc _ _ _
  apply pullback.hom_ext
  · simp only [bcMap, pullback.map, Category.assoc, pullback.lift_fst, Category.comp_id, eIso_fst]
    rw [← e1, Spec.map_comp, Category.assoc]
  · simp only [bcMap, pullback.map, Category.assoc, pullback.lift_snd, eIso_snd]
    rw [← Category.assoc, eIso_snd, ← Spec.map_comp, ← e2, Spec.map_comp]

theorem AffRing_of : LateralTheory.KummerTheory.ContCut.AffRing := by
  intro X _ R p
  refine ⟨Tf p, ⟨NatIso.ofComponents (fun A => (eIso p A).op) ?_⟩, fun A => ⟨A.hom ≫ pushout.inl A.hom (phi p)⟩, ?_⟩
  · intro A B h
    exact Quiver.Hom.unop_inj (nat p h)
  · intro J _ _ D c hc
    have : IsConnected J := IsFiltered.isConnected J
    have hc' : IsColimit c := isColimitOfReflects (Under.forget R) hc
    let _ : PreservesColimitsOfSize.{0, 0} (Under.pushout (phi p)) :=
      (Under.mapPushoutAdj (phi p)).leftAdjoint_preservesColimits
    have : PreservesColimit D (Tf p) :=
      inferInstanceAs (PreservesColimit D (Under.pushout (phi p) ⋙ Under.forget _))
    exact ⟨isColimitOfPreserves (Tf p) hc'⟩

end LateralTheory.KummerTheory.AffRingPf
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.BcHomIsPullback
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.BCPf
open LateralTheory.KummerTheory.ContCut

@[reassoc] theorem bcHom_fst {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) :
    bcHom f p r e s ≫ pullback.fst p (Spec.map s) = pullback.fst r (Spec.map s) ≫ f := by
  unfold bcHom pullback.map; exact pullback.lift_fst _ _ _

theorem bcHom_snd {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) :
    bcHom f p r e s ≫ pullback.snd p (Spec.map s) = pullback.snd r (Spec.map s) := by
  unfold bcHom pullback.map; rw [pullback.lift_snd, Category.comp_id]

theorem bcHom_isPullback {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) :
    IsPullback (bcHom f p r e s) (pullback.fst r (Spec.map s)) (pullback.fst p (Spec.map s)) f := by
  have big : IsPullback (bcHom f p r e s ≫ pullback.snd p (Spec.map s)) (pullback.fst r (Spec.map s))
      (Spec.map s) (f ≫ p) := by
    rw [bcHom_snd, e]; exact (IsPullback.of_hasPullback r (Spec.map s)).flip
  exact IsPullback.of_right big (bcHom_fst f p r e s) (IsPullback.of_hasPullback p (Spec.map s)).flip

theorem bcHom_open {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) [IsOpenImmersion f] : IsOpenImmersion (bcHom f p r e s) :=
  MorphismProperty.of_isPullback (bcHom_isPullback f p r e s).flip ‹_›

theorem bcHom_range {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) (x : ↥(pullback p (Spec.map s))) (hx : pullback.fst p (Spec.map s) x ∈ Set.range f) :
    x ∈ Set.range (bcHom f p r e s) := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨q, hq, -⟩ := Scheme.exists_preimage_of_isPullback (bcHom_isPullback f p r e s) x u hu.symm
  exact ⟨q, hq⟩

theorem BC_of : BC := by
  intro R A s W U V X a b f g p pU pV pW ea eb ef eg h
  obtain ⟨hf, hg, hpb, hcov⟩ := h
  refine ⟨bcHom_open f p pU ef s, bcHom_open g p pV eg s, ?_, ?_⟩
  · have sq1 : IsPullback (pullback.fst pW (Spec.map s)) (bcHom b pV pW eb s) b (pullback.fst pV (Spec.map s)) :=
      (bcHom_isPullback b pV pW eb s).flip
    have big0 := sq1.paste_horiz hpb
    have big : IsPullback (bcHom a pU pW ea s ≫ pullback.fst pU (Spec.map s)) (bcHom b pV pW eb s) f
        (bcHom g p pV eg s ≫ pullback.fst p (Spec.map s)) := by
      rw [bcHom_fst, bcHom_fst]; exact big0
    refine IsPullback.of_right big ?_ (bcHom_isPullback f p pU ef s).flip
    apply pullback.hom_ext
    · simp only [Category.assoc, bcHom_fst, bcHom_fst_assoc]; rw [hpb.w]
    · simp only [Category.assoc, bcHom_snd]
  · intro x
    rcases hcov (pullback.fst p (Spec.map s) x) with hx | hx
    · exact Or.inl (bcHom_range f p pU ef s x hx)
    · exact Or.inr (bcHom_range g p pV eg s x hx)

end LateralTheory.KummerTheory.BCPf
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.ConeAlgPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ConeAlgPf
open LateralTheory.KummerTheory.LHCut

variable {Λ : Type} [CommRing Λ]

theorem sres_comp {F : Shv Λ} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res h (Sec.res g a) = Sec.res (h ≫ g) a := by
  show (F.obj.map h.op).hom ((F.obj.map g.op).hom a) = (F.obj.map (h ≫ g).op).hom a
  rw [op_comp, Functor.map_comp]
  rfl

theorem smap_res {F G : Shv Λ} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) :=
  (congrArg (fun k => k.hom a) (φ.hom.naturality g.op)).symm

theorem smap_comp {F G H : Shv Λ} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map ψ (Sec.map φ a) = Sec.map (φ ≫ ψ) a := rfl

theorem dd {C : Cx Λ} (i j k : ℤ) {U : Scheme.{0}} (a : Sec (C.X i) U) :
    Sec.map (C.d j k) (Sec.map (C.d i j) a) = 0 := by
  rw [smap_comp, HomologicalComplex.d_comp_d]; rfl

theorem leib' {I J K : Cx Λ} (μ : Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U)
    (b : Sec (J.X t) U) (ha : Sec.map (I.d s (s + 1)) a = 0) (t' w' : ℤ) (ht : t + 1 = t') (hw : w + 1 = w') :
    Sec.map (K.d w w') (μ.mul U s t w h a b) = s.negOnePow • μ.mul U s t' w' (by omega) a (Sec.map (J.d t t') b) := by
  subst ht; subst hw
  rw [μ.leibniz, ha, map_zero, LinearMap.zero_apply, zero_add]

theorem rst_fst {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) :
    rst p g ≫ pullback.fst p U.hom = pullback.fst p V.hom := by
  simp only [rst, pullback.map]; erw [pullback.lift_fst]; simp

theorem rst_snd {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) :
    rst p g ≫ pullback.snd p U.hom = pullback.snd p V.hom ≫ g.left := by
  simp only [rst, pullback.map]; erw [pullback.lift_snd]

theorem rst_comp {X S : Scheme.{0}} (p : X ⟶ S) {W V U : Over S} (g' : W ⟶ V) (g : V ⟶ U) :
    rst p (g' ≫ g) = rst p g' ≫ rst p g := by
  apply pullback.hom_ext
  · rw [Category.assoc, rst_fst, rst_fst, rst_fst]
  · rw [Category.assoc, rst_snd, rst_snd, ← Category.assoc, rst_snd, Category.assoc, Over.comp_left]

theorem smap_add {F G : Shv Λ} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ _ _
theorem smap_sub {F G : Shv Λ} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a - b) = Sec.map φ a - Sec.map φ b := map_sub _ _ _
theorem smap_smul {F G : Shv Λ} (φ : F ⟶ G) {U : Scheme.{0}} (c : ULift.{1} Λ) (a : Sec F U) :
    Sec.map φ (c • a) = c • Sec.map φ a := map_smul _ _ _
theorem smap_sum {F G : Shv Λ} (φ : F ⟶ G) {U : Scheme.{0}} {ι : Type*} (t : Finset ι) (f : ι → Sec F U) :
    Sec.map φ (∑ i ∈ t, f i) = ∑ i ∈ t, Sec.map φ (f i) := map_sum _ _ _
theorem sres_sub {F : Shv Λ} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a - b) = Sec.res g a - Sec.res g b := map_sub _ _ _
theorem sres_zero {F : Shv Λ} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _
theorem sres_sum {F : Shv Λ} {V U : Scheme.{0}} (g : V ⟶ U) {ι : Type*} (t : Finset ι) (f : ι → Sec F U) :
    Sec.res g (∑ i ∈ t, f i) = ∑ i ∈ t, Sec.res g (f i) := map_sum _ _ _

section Main
variable {I J K : Cx Λ} {r : ℕ → ℕ} {M : ℕ}

theorem usmul_map {F G : Shv Λ} (φ : F ⟶ G) {U : Scheme.{0}} (u : ℤˣ) (a : Sec F U) :
    Sec.map φ (u • a) = u • Sec.map φ a := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

theorem usmul_res {F : Shv Λ} {V U : Scheme.{0}} (g : V ⟶ U) (u : ℤˣ) (a : Sec F U) :
    Sec.res g (u • a) = u • Sec.res g a := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

theorem dS_add (n m : ℤ) {U : Scheme.{0}} (b b' : FinalTheorems J r M n U) : dS n m (b + b') = dS n m b + dS n m b' := by
  funext a s
  simp only [dS, Pi.add_apply]
  rw [smap_add, smul_add]

theorem dS_smul (n m : ℤ) {U : Scheme.{0}} (c : ULift.{1} Λ) (b : FinalTheorems J r M n U) : dS n m (c • b) = c • dS n m b := by
  funext a s
  simp only [dS, Pi.smul_apply]
  rw [smap_smul, Units.smul_def, Units.smul_def, smul_comm]

theorem dS_dS (n m k : ℤ) {U : Scheme.{0}} (b : FinalTheorems J r M n U) : dS m k (dS n m b) = 0 := by
  funext a s
  simp only [dS, Pi.zero_apply]
  rw [usmul_map, dd, smul_zero, smul_zero]

variable (μ : Pair I J K) {X S : Scheme.{0}} (p : X ⟶ S) (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X)

theorem Phi_add (n w : ℤ) (h : n = w) (U : Over S) (b b' : FinalTheorems J r M n U.left) :
    Phi μ p γ n w h U (b + b') = Phi μ p γ n w h U b + Phi μ p γ n w h U b' := by
  simp only [Phi, Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]

theorem Phi_smul (n w : ℤ) (h : n = w) (U : Over S) (c : ULift.{1} Λ) (b : FinalTheorems J r M n U.left) :
    Phi μ p γ n w h U (c • b) = c • Phi μ p γ n w h U b := by
  simp only [Phi, Pi.smul_apply, map_smul, Finset.smul_sum]

theorem d_Phi (hγ : Closed γ) (n w : ℤ) (h : n = w) (n' w' : ℤ) (hn : n + 1 = n') (hw : w + 1 = w') (U : Over S)
    (b : FinalTheorems J r M n U.left) :
    Sec.map (K.d w w') (Phi μ p γ n w h U b) = Phi μ p γ n' w' (by omega) U (dS n n' b) := by
  simp only [Phi, dS]
  rw [smap_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [smap_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have ha : Sec.map (I.d ((a : ℕ) : ℤ) ((a : ℕ) + 1)) (Sec.res (pullback.fst p U.hom) (γ a s)) = 0 := by
    rw [← smap_res, hγ]; exact sres_zero _
  rw [leib' μ _ _ _ _ _ _ _ ha (n' - ((a : ℕ) : ℤ)) w' (by omega) hw, usmul_res, smap_res, Units.smul_def,
    Units.smul_def, map_zsmul]

theorem Phi_res (n w : ℤ) (h : n = w) {V U : Over S} (g : V ⟶ U) (b : FinalTheorems J r M n U.left) :
    Sec.res (rst p g) (Phi μ p γ n w h U b) = Phi μ p γ n w h V (fun a s => Sec.res g.left (b a s)) := by
  simp only [Phi]
  rw [sres_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [sres_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [μ.nat, sres_comp, sres_comp, sres_comp, rst_fst, rst_snd]

end Main

theorem coneAlg_of : ConeAlg := by
  intro Λ _ I J K μ X S p r M γ hγ j j' h U
  refine ⟨⟨fun x y => ?_, fun c x => ?_⟩, fun j'' h' x => ?_, fun V g => ⟨⟨fun x y => ?_, fun c x => ?_⟩, fun x => ?_,
    fun W g' x => ?_⟩⟩
  · refine Prod.ext (dS_add _ _ _ _) ?_
    show Phi μ p γ _ _ h U (x.1 + y.1) - Sec.map (K.d j j') (x.2 + y.2) = _
    rw [Phi_add, smap_add, add_sub_add_comm]; rfl
  · refine Prod.ext (dS_smul _ _ _ _) ?_
    show Phi μ p γ _ _ h U (c • x.1) - Sec.map (K.d j j') (c • x.2) = _
    rw [Phi_smul, smap_smul, ← smul_sub]; rfl
  · refine Prod.ext (dS_dS _ _ _ _) ?_
    show Phi μ p γ _ _ h' U (dS _ _ x.1) - Sec.map (K.d j' j'') (Phi μ p γ _ _ h U x.1 - Sec.map (K.d j j') x.2) = 0
    rw [smap_sub, d_Phi μ p γ hγ (j + 1) j' h (j' + 1) j'' (by omega) h', dd, sub_zero, sub_self]
  · refine Prod.ext ?_ (map_add _ _ _)
    funext a s; exact map_add _ _ _
  · refine Prod.ext ?_ (map_smul _ _ _)
    funext a s; exact map_smul _ _ _
  · refine Prod.ext ?_ ?_
    · funext a s
      show Sec.res g.left (_ • Sec.map _ _) = _ • Sec.map _ (Sec.res g.left _)
      rw [usmul_res, smap_res]
    · show Sec.res (rst p g) (Phi μ p γ _ _ h U x.1 - Sec.map (K.d j j') x.2) =
        Phi μ p γ _ _ h V (fun a s => Sec.res g.left (x.1 a s)) - Sec.map (K.d j j') (Sec.res (rst p g) x.2)
      rw [sres_sub, Phi_res, smap_res]
  · refine Prod.ext ?_ ?_
    · funext a s
      show Sec.res (g' ≫ g).left _ = Sec.res g'.left (Sec.res g.left _)
      rw [Over.comp_left, sres_comp]
    · show Sec.res (rst p (g' ≫ g)) x.2 = Sec.res (rst p g') (Sec.res (rst p g) x.2)
      rw [rst_comp, sres_comp]

end LateralTheory.KummerTheory.ConeAlgPf
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.CorepPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.KummerTheory.LHCut

theorem corep_of : Corep := by
  intro Λ _ S U
  let M : ModuleCat.{1} (ULift.{1} Λ) := ModuleCat.of (ULift.{1} Λ) (ULift.{1} Λ)
  let P : SlShv Λ S := Sheaf.freeYoneda (Scheme.etaleTopology.over S) U M
  have key : ∀ (F : SlShv Λ S) (φ : P ⟶ F),
      Sheaf.freeYonedaHomEquiv φ = Sheaf.freeYonedaHomEquiv (𝟙 P) ≫ φ.hom.app (op U) := by
    intro F φ
    conv_lhs => rw [← Category.id_comp φ]
    simp only [Sheaf.freeYonedaHomEquiv]
    rfl
  refine ⟨P, (Sheaf.freeYonedaHomEquiv (𝟙 P)).hom 1, fun F => ?_⟩
  have e : (fun φ : P ⟶ F => (φ.hom.app (op U)).hom ((Sheaf.freeYonedaHomEquiv (𝟙 P)).hom 1)) =
      (fun g : M ⟶ F.obj.obj (op U) => g.hom 1) ∘ Sheaf.freeYonedaHomEquiv := by
    funext φ
    simp only [Function.comp_apply, key F φ]
    rfl
  rw [e]
  refine Function.Bijective.comp ⟨fun g h hgh => ?_, fun n => ?_⟩ (Equiv.bijective _)
  · refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    have : x = x • (1 : ULift.{1} Λ) := (mul_one x).symm
    rw [this, map_smul, map_smul]
    exact congrArg (x • ·) hgh
  · exact ⟨ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} Λ) _ n), one_smul _ n⟩

end LateralTheory.KummerTheory.LHCut
end
end

