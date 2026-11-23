module

public import Development.EtaleCohomology.KummerTheory.Bundle0001

@[expose] public section

-- bundled from Development.EtaleCohomology.KummerTheory.DictPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def EvLin : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ},
  (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x,
    ev (R := R) (α + β) p s h U x = ev (R := R) α p s h U x + ev (R := R) β p s h U x ∧ ev (R := R) (-α) p s h U x = -ev (R := R) α p s h U x) ∧
  (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
    Sec.res g (ev (R := R) α p s h U x) = ev (R := R) α p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x)) ∧
  ∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U),
    ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x =
      ev (R := R) α p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x)

def DictExist : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) (X : Scheme.{0}) (n : ℤ) (a : Sec (I.X n) X),
  Sec.map (I.d n (n + 1)) a = 0 → ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n,
    ev (R := R) α.1 0 n (by simp) X (𝟙 X) = a ∧
    ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : Sx (sch.obj X) (p + 1) U), ev (R := R) α.1 (p + 1) s h U y = 0

def DictNormal : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) (X : Scheme.{0}) (n : ℤ)
  (α : Cocycle ((chains R).obj (sch.obj X)) I n), ∃ α' : Cocycle ((chains R).obj (sch.obj X)) I n,
    CohomologyClass.mk α' = CohomologyClass.mk α ∧
    ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : Sx (sch.obj X) (p + 1) U), ev (R := R) α'.1 (p + 1) s h U y = 0

def DictZero : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) (X : Scheme.{0}) (n : ℤ)
  (α : Cocycle ((chains R).obj (sch.obj X)) I n),
  (∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : Sx (sch.obj X) (p + 1) U), ev (R := R) α.1 (p + 1) s h U y = 0) →
  Sec.map (I.d n (n + 1)) (ev (R := R) α.1 0 n (by simp) X (𝟙 X)) = 0 ∧
    (CohomologyClass.mk α = 0 ↔ ∃ b : Sec (I.X (n - 1)) X, Sec.map (I.d (n - 1) n) b = ev (R := R) α.1 0 n (by simp) X (𝟙 X))

theorem Dict_of (hL : EvLin) (hE : DictExist) (hN : DictNormal) (hZ : DictZero) : Dict := by
  intro R _ I X n
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨α, h0, h1⟩ := hE R I X n a ha
    exact ⟨_, α, rfl, h0, h1⟩
  · intro x
    obtain ⟨α, rfl⟩ := x.mk_surjective
    obtain ⟨α', e, h1⟩ := hN R I X n α
    exact ⟨_, α', e, rfl, h1⟩
  · rintro x a ⟨α, rfl, h0, h1⟩
    subst h0
    exact hZ R I X n α h1
  · rintro x x' a a' ⟨α, rfl, h0, h1⟩ ⟨α', rfl, h0', h1'⟩
    refine ⟨⟨α + α', CohomologyClass.mk_add _ _ |>.symm, ?_, ?_⟩, ⟨-α, ?_, ?_, ?_⟩⟩
    · rw [← h0, ← h0']; exact ((hL R).1 α.1 α'.1 0 n _ X (𝟙 X)).1
    · intro p s h U y
      rw [show ((α + α' : Cocycle _ _ n) : Cochain _ _ n) = α.1 + α'.1 from rfl, ((hL R).1 _ _ _ _ _ _ _).1, h1, h1', add_zero]
    · rw [← CohomologyClass.mk_neg]
    · rw [← h0]; exact ((hL R).1 α.1 α.1 0 n _ X (𝟙 X)).2
    · intro p s h U y
      rw [show ((-α : Cocycle _ _ n) : Cochain _ _ n) = -α.1 from rfl, ((hL R).1 α.1 α.1 _ _ _ _ _).2, h1, neg_zero]
  · rintro Y f x a ⟨α, rfl, h0, h1⟩
    refine ⟨zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n), rfl, ?_, ?_⟩
    · change ev (R := R) ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add n)) 0 n _ Y (𝟙 Y) = _
      refine ((hL R).2.2 (sch.map f) α.1 0 n _ Y (𝟙 Y)).trans ?_
      rw [← h0]
      exact (((hL R).2.1 α.1 0 n _ Y X f (𝟙 X)).trans rfl).symm
    · intro p s h U y
      change ev (R := R) ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add n)) (p + 1) s h U y = 0
      exact ((hL R).2.2 (sch.map f) α.1 _ _ _ _ _).trans (h1 _ _ _ _ _)

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.EtaleKummerDegreeZeroCohomologyOfTwistSectionCla
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def Cls0 : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})
  (α β : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0),
  ev α.1 0 0 (by simp) X (𝟙 X) = ev β.1 0 0 (by simp) X (𝟙 X) → CohomologyClass.mk α = CohomologyClass.mk β

def OneEx : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
  ∃ c : Ht q (sp A) 0 0, ∃ α : Cocycle ((chains (ZMod q)).obj (sp A)) (res (ZMod q) (tw q 0)) 0,
    CohomologyClass.mk α = c ∧
    ∀ (U : Scheme.{0}) (x : Sx (sp A) 0 U) (ζ : Prim q Γ(U, ⊤)),
      ev α.1 0 0 (by simp) U x = resGen 0 ζ

theorem etale_kummer_degree_zero_cohomology_of_twist_section_class_and_root_ex (hT : TwSec) (hC : Cls0) (hO : OneEx) : H0 := by
  intro h9 q _ A _ hA hq
  obtain ⟨hne, hb⟩ := hT q A hA hq
  obtain ⟨ζ⟩ := hne
  have hb0 := hb 0 ζ
  obtain ⟨_, e, -, he⟩ := h9 (ZMod q) (tw q 0)
  have hone : one q (sp A) = e (Spec (CommRingCat.of A)) (twGen 0 ζ) := by
    obtain ⟨α, hα, hv⟩ := pick_spec (hO q A hA hq)
    have hα' : CohomologyClass.mk α = one q (sp A) := hα
    obtain ⟨β, hβ, hβv⟩ := he (Spec (CommRingCat.of A)) (twGen 0 ζ)
    rw [← hα', ← hβ]
    exact hC _ _ _ α β ((hv _ (𝟙 _) ζ).trans hβv.symm)
  have hlin : ∀ t : ZMod q, t • one q (sp A) =
      e (Spec (CommRingCat.of A)) ((ULift.up t : ULift.{1} (ZMod q)) • twGen 0 ζ) := by
    intro t
    rw [hone]
    have h1 : t = ((t.val : ℕ) : ZMod q) := (ZMod.natCast_zmod_val t).symm
    have h2 : (ULift.up t : ULift.{1} (ZMod q)) = ((t.val : ℕ) : ULift.{1} (ZMod q)) := by
      apply ULift.ext
      rw [ULift.down_natCast]; exact h1
    rw [h2, Nat.cast_smul_eq_nsmul, map_nsmul]
    conv_lhs => rw [h1]
    rw [Nat.cast_smul_eq_nsmul]
  have hfun : (fun t : ZMod q => t • one q (sp A)) =
      (e (Spec (CommRingCat.of A))) ∘ (fun t : ZMod q => (ULift.up t : ULift.{1} (ZMod q)) • twGen 0 ζ) := funext hlin
  rw [hfun]
  exact (e _).bijective.comp hb0

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.GhostPf
section
open CategoryTheory Limits

namespace LateralTheory.KummerTheory.GhostPf

variable {A : Type*} [Category A] [Abelian A]

theorem cyc (C : CochainComplex A ℤ) (N : ℕ) {j k l : ℤ} (hjk : j + 1 = k) (hkl : k + 1 = l)
    (hH : N • 𝟙 (C.homology k) = 0) {I : A} (φ : C.X k ⟶ I) (hφ : C.d j k ≫ φ = 0)
    {P : A} (f : P ⟶ C.X k) (hf : f ≫ C.d k l = 0) : f ≫ (N • φ) = 0 := by
  rw [← C.liftCycles_i f l ((ComplexShape.up ℤ).next_eq' hkl) hf,
    ← C.p_descOpcycles φ j ((ComplexShape.up ℤ).prev_eq' hjk) hφ]
  have e : C.iCycles k ≫ (N • (C.pOpcycles k ≫ C.descOpcycles φ j ((ComplexShape.up ℤ).prev_eq' hjk) hφ)) =
      C.homologyπ k ≫ (N • 𝟙 (C.homology k)) ≫ C.homologyι k ≫
        C.descOpcycles φ j ((ComplexShape.up ℤ).prev_eq' hjk) hφ := by
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp]
    rw [← Category.assoc (C.iCycles k), ← C.homology_π_ι, Category.assoc]
  rw [Category.assoc, e, hH]
  simp

theorem extd (C : CochainComplex A ℤ) (N : ℕ) {j k l : ℤ} (hjk : j + 1 = k) (hkl : k + 1 = l)
    (hH : N • 𝟙 (C.homology k) = 0) {I : A} [Injective I] (φ : C.X k ⟶ I) (hφ : C.d j k ≫ φ = 0) :
    ∃ c : C.X l ⟶ I, C.d k l ≫ c = N • φ := by
  have hk : kernel.ι (factorThruImage (C.d k l)) ≫ (N • φ) = 0 := by
    apply cyc C N hjk hkl hH φ hφ
    calc kernel.ι (factorThruImage (C.d k l)) ≫ C.d k l
        = (kernel.ι (factorThruImage (C.d k l)) ≫ factorThruImage (C.d k l)) ≫ image.ι (C.d k l) := by
          rw [Category.assoc, image.fac]
      _ = 0 := by rw [kernel.condition, zero_comp]
  refine ⟨Injective.factorThru (Abelian.epiDesc _ _ hk) (image.ι (C.d k l)), ?_⟩
  calc C.d k l ≫ _ = factorThruImage (C.d k l) ≫ image.ι (C.d k l) ≫
        Injective.factorThru (Abelian.epiDesc _ _ hk) (image.ι (C.d k l)) := by
          rw [← Category.assoc, image.fac]
    _ = N • φ := by rw [Injective.comp_factorThru, Abelian.comp_epiDesc]

theorem step (C : CochainComplex A ℤ) (N M : ℕ) {i j k l : ℤ} (_hij : i + 1 = j) (hjk : j + 1 = k)
    (hkl : k + 1 = l) (hH : N • 𝟙 (C.homology k) = 0) [Injective (C.X k)]
    (a : C.X j ⟶ C.X i) (b : C.X k ⟶ C.X j) (hab : a ≫ C.d i j + C.d j k ≫ b = M • 𝟙 (C.X j)) :
    ∃ c : C.X l ⟶ C.X k, (N • b) ≫ C.d j k + C.d k l ≫ c = (N * M) • 𝟙 (C.X k) := by
  have hdb : C.d j k ≫ b = M • 𝟙 (C.X j) - a ≫ C.d i j := by rw [← hab]; abel
  have hφ : C.d j k ≫ (M • 𝟙 (C.X k) - b ≫ C.d j k) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc, hdb, Preadditive.sub_comp, Category.assoc,
      HomologicalComplex.d_comp_d]
    simp
  obtain ⟨c, hc⟩ := extd C N hjk hkl hH _ hφ
  refine ⟨c, ?_⟩
  rw [hc, Preadditive.nsmul_comp, smul_sub, mul_smul]
  abel

theorem homot (C : CochainComplex A ℤ) [C.IsStrictlyGE (-1)] (hI : ∀ j, Injective (C.X j)) (N m : ℕ)
    (hH : ∀ j : ℤ, j < m → N • 𝟙 (C.homology j) = 0) :
    ∀ n : ℕ, ∀ i j k : ℤ, i + 1 = j → j + 1 = k → j = (n : ℤ) - 1 → j < m →
      ∃ a : C.X j ⟶ C.X i, ∃ b : C.X k ⟶ C.X j, a ≫ C.d i j + C.d j k ≫ b = N ^ (n + 1) • 𝟙 (C.X j) := by
  intro n
  induction n with
  | zero =>
    intro i j k hij hjk hj hjm
    have hj' : j = -1 := by simpa using hj
    subst hj'
    have := hI (-1)
    have hz : C.d i (-1) ≫ 𝟙 (C.X (-1)) = 0 :=
      (C.isZero_of_isStrictlyGE (-1) i (by omega)).eq_of_src _ _
    obtain ⟨c, hc⟩ := extd C N hij hjk (hH _ hjm) (𝟙 _) hz
    exact ⟨0, c, by simp [hc]⟩
  | succ n ih =>
    intro i j k hij hjk hj hjm
    subst hij
    obtain ⟨a, b, hab⟩ := ih (i - 1) i (i + 1) (by ring) rfl (by push_cast at hj; omega) (by omega)
    have := hI (i + 1)
    obtain ⟨c, hc⟩ := step C N (N ^ (n + 1)) (by ring : i - 1 + 1 = i) rfl hjk (hH _ hjm) a b hab
    exact ⟨N • b, c, by rw [hc, ← pow_succ']⟩

theorem Ghost_of : LateralTheory.KummerTheory.Ghost := by
  intro A _ _ _ C _ hI N m hH j hj P f hf
  by_cases hlow : j < -1
  · refine ⟨0, ?_⟩
    exact (C.isZero_of_isStrictlyGE (-1) j hlow).eq_of_tgt _ _
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, j = (n : ℤ) - 1 := ⟨(j + 1).toNat, by omega⟩
    obtain ⟨a, b, hab⟩ := homot C hI N m hH n (j - 1) j (j + 1) (by ring) rfl hn hj
    have hnm : n + 1 ≤ m + 1 := by omega
    refine ⟨N ^ (m + 1 - (n + 1)) • (f ≫ a), ?_⟩
    have e : f ≫ a ≫ C.d (j - 1) j = N ^ (n + 1) • f := by
      have := congrArg (f ≫ ·) hab
      simp only [Preadditive.comp_add, Preadditive.comp_nsmul, Category.comp_id] at this
      rw [← Category.assoc f (C.d j (j + 1)) b, hf, zero_comp, add_zero] at this
      exact this
    rw [Preadditive.nsmul_comp, Category.assoc, e, smul_smul, ← pow_add, Nat.sub_add_cancel hnm]

end LateralTheory.KummerTheory.GhostPf
end

-- bundled from Development.EtaleCohomology.KummerTheory.InjSlicePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def ForgetInj : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) [Injective F] (S : Scheme.{0}),
  ∃ h : Presheaf.IsSheaf (Scheme.etaleTopology.over S) ((Over.forget S).op ⋙ F.obj),
    Injective (⟨_, h⟩ : Sheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} R)))

theorem pushPullback_inj {R : Type} [CommRing R] {X S : Scheme.{0}} (p : X ⟶ S)
    (G : Sheaf (Scheme.etaleTopology.over X) (ModuleCat.{1} (ULift.{1} R))) [Injective G] :
    Injective (((Over.pullback p).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R))
      (Scheme.etaleTopology.over S) (Scheme.etaleTopology.over X)).obj G) := by
  have adj := (Over.mapPullbackAdj p).sheafPushforwardContinuous (E := ModuleCat.{1} (ULift.{1} R))
    (Scheme.etaleTopology.over X) (Scheme.etaleTopology.over S)
  have : ((Over.map p).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R))
      (Scheme.etaleTopology.over X) (Scheme.etaleTopology.over S)).PreservesMonomorphisms := inferInstance
  exact Injective.injective_of_adjoint adj G

theorem InjSlice_of (hF : ForgetInj) : InjSlice := by
  intro R _ F _ X S p
  obtain ⟨hX, iX⟩ := hF R F X
  refine ⟨?_, hF R F S⟩
  let G : Sheaf (Scheme.etaleTopology.over X) (ModuleCat.{1} (ULift.{1} R)) := ⟨_, hX⟩
  exact ⟨(((Over.pullback p).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R))
      (Scheme.etaleTopology.over S) (Scheme.etaleTopology.over X)).obj G).2, pushPullback_inj p G⟩

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.InsepPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.KummerTheory.InsepPf

theorem res_comp {R : Type} [CommRing R] (F : Shv R) {W V U : Scheme.{0}} (g : W ⟶ V) (h : V ⟶ U) (x : Sec F U) :
    Sec.res (g ≫ h) x = Sec.res g (Sec.res h x) := by
  simp [Sec.res]

theorem res_id {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (x : Sec F U) : Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

theorem res_bij_iso {R : Type} [CommRing R] (F : Shv R) {V U : Scheme.{0}} (e : V ≅ U) :
    Function.Bijective (Sec.res (F := F) e.hom) := by
  refine Function.bijective_iff_has_inverse.2 ⟨Sec.res e.inv, fun x => ?_, fun x => ?_⟩
  · rw [← res_comp, e.inv_hom_id, res_id]
  · rw [← res_comp, e.hom_inv_id, res_id]

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (Prim.map (Scheme.Γ.map g.op).hom ζ) := by
  have h := congrArg (fun f => f.hom (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q))) : (twF q i).obj Γ(U, ⊤)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  simp only [ModuleCat.hom_comp] at h
  unfold twGen ofRings.sec
  refine h.symm.trans ?_
  show ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom
    (((Scheme.Γ ⋙ twF q i).map g.op).hom (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q))))) = _
  refine congrArg ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom ?_
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map g.op).hom) (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))) = _
  exact congrArg _ (Finsupp.mapDomain_single (f := Prim.map (Scheme.Γ.map g.op).hom) (a := ζ) (b := (1 : ULift.{1} (ZMod q))))

theorem res_smul {R : Type} [CommRing R] (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) (c : ULift.{1} R) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x := map_smul (F.obj.map g.op).hom c x

theorem res_spec_bij (hTw : TwSec) (q : ℕ) [NeZero q] {A B : Type} [CommRing A] [CommRing B] (hA : SH A) (hB : SH B)
    (hq : IsUnit (q : A)) (φ : A →+* B) (i : ℤ) :
    Function.Bijective (Sec.res (F := tw q i) (Spec.map (CommRingCat.ofHom φ))) := by
  have hqB : IsUnit (q : B) := by simpa using hq.map φ
  obtain ⟨⟨ζ⟩, hζ⟩ := hTw q A hA hq
  have h1 := hζ i ζ
  have h2 := (hTw q B hB hqB).2 i (Prim.map (Scheme.Γ.map (Spec.map (CommRingCat.ofHom φ)).op).hom ζ)
  have e : (Sec.res (F := tw q i) (Spec.map (CommRingCat.ofHom φ))) ∘
      (fun t : ZMod q => (ULift.up t : ULift.{1} (ZMod q)) • twGen i ζ) =
      fun t : ZMod q => (ULift.up t : ULift.{1} (ZMod q)) •
        twGen i (Prim.map (Scheme.Γ.map (Spec.map (CommRingCat.ofHom φ)).op).hom ζ) := by
    funext t
    simp only [Function.comp]
    rw [res_smul, twGen_res]
    rfl
  exact (Function.Bijective.of_comp_iff _ h1).1 (by rw [e]; exact h2)

theorem res_bij (hTw : TwSec) (q : ℕ) [NeZero q] (i : ℤ) {P Q : Scheme.{0}} (m : P ⟶ Q) {A B : Type} [CommRing A]
    [CommRing B] (hA : SH A) (hB : SH B) (hq : IsUnit (q : A)) (iP : P ≅ Spec (CommRingCat.of B))
    (iQ : Q ≅ Spec (CommRingCat.of A)) : Function.Bijective (Sec.res (F := tw q i) m) := by
  set g' := iP.inv ≫ m ≫ iQ.hom
  have hm : m = iP.hom ≫ Spec.map (CommRingCat.ofHom (Spec.preimage g').hom) ≫ iQ.inv := by
    simp [g']
  have hg := res_spec_bij hTw q hA hB hq (Spec.preimage g').hom i
  have : (Sec.res (F := tw q i) m) = Sec.res iP.hom ∘ Sec.res (Spec.map (CommRingCat.ofHom (Spec.preimage g').hom)) ∘
      Sec.res (F := tw q i) iQ.inv := by
    funext x
    simp only [Function.comp]
    rw [hm, res_comp, res_comp]
  rw [this]
  exact (res_bij_iso _ iP).comp (hg.comp (res_bij_iso _ iQ.symm))

theorem sub_of_iso {R : Type} [CommRing R] (F : Shv R) (n : ℤ) {P : Scheme.{0}} {B : Type} [CommRing B]
    (e : P ≅ Spec (CommRingCat.of B)) (h : Subsingleton (H R (sp B) F n)) : Subsingleton (H R (sch.obj P) F n) := by
  refine ⟨fun x y => ?_⟩
  have hx : ∀ z : H R (sch.obj P) F n, z = pull R (sch.map e.hom) F n (pull R (sch.map e.inv) F n z) := fun z => by
    rw [← pull_comp, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [hx x, hx y, Subsingleton.elim (pull R (sch.map e.inv) F n x) (pull R (sch.map e.inv) F n y)]

theorem bij_of_sub {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G →+ G') (h : Subsingleton G)
    (h' : Subsingleton G') : Function.Bijective f :=
  ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

theorem eqv_of (hA9 : A9) (hB2 : B2) (hTw : TwSec) (q : ℕ) [NeZero q] (i : ℤ) {P Q : Scheme.{0}} (m : P ⟶ Q)
    {A B : Type} [CommRing A] [CommRing B] (hA : SH A) (hB : SH B) (hq : IsUnit (q : A))
    (iP : P ≅ Spec (CommRingCat.of B)) (iQ : Q ≅ Spec (CommRingCat.of A)) : Eqv _ (sch.map m) (tw q i) := by
  intro n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · exact bij_of_sub _ ((hA9 _ (tw q i)).1 _ n hn) ((hA9 _ (tw q i)).1 _ n hn)
  · obtain ⟨e, he, -⟩ := (hA9 _ (tw q i)).2
    have h0 := res_bij hTw q i m hA hB hq iP iQ
    have : (pull _ (sch.map m) (tw q i) 0 : _ → _) = e P ∘ Sec.res m ∘ (e Q).symm := by
      funext x
      simp only [Function.comp]
      rw [← he, AddEquiv.apply_symm_apply]
    rw [this]
    exact (e P).bijective.comp (h0.comp (e Q).symm.bijective)
  · exact bij_of_sub _ (sub_of_iso _ n iQ (hB2 _ A hA _ n hn)) (sub_of_iso _ n iP (hB2 _ B hB _ n hn))

theorem Insep_of (hSH : SHInsep) (hTw : TwSec) : Insep := by
  intro hA9 hB2 hB3 q _ κ K _ _ _ _ hq X p i
  have hqX : IsUnit (q : Γ(X, ⊤)) := by
    have h1 : IsUnit (q : Γ(Spec (CommRingCat.of κ), ⊤)) := by
      simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom
    simpa using h1.map (p.appTop).hom
  refine hB3 q (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap κ K)))) (𝟙 X) hqX i ?_
  intro A _ s hA
  let _ : Algebra κ A := (Spec.preimage (s ≫ p)).hom.toAlgebra
  have hsp : s ≫ p = Spec.map (CommRingCat.ofHom (algebraMap κ A)) := (Spec.map_preimage _).symm
  have hqA : IsUnit (q : A) := by simpa using hq.map (algebraMap κ A)
  refine eqv_of hA9 hB2 hTw q i _ hA (hSH κ K A hA) hqA ?_ (asIso (pullback.snd (𝟙 X) s))
  exact pullback.congrHom (Category.comp_id _) rfl ≪≫ pullbackSymmetry _ _ ≪≫
    pullbackRightPullbackFstIso p _ s ≪≫ pullback.congrHom hsp rfl ≪≫ pullbackSpecIso κ A K

end LateralTheory.KummerTheory.InsepPf
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.InvOfField
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

theorem IsoUpTo.comb_mono {q : ℕ} {E : Spc} {n i : ℤ} {r : ℕ} {c : Fin r → Ht q E n i} {N N' : ℕ} (hd : N ∣ N')
    (h : IsoUpTo N (comb q c)) : IsoUpTo N' (comb q c) := by
  obtain ⟨m, rfl⟩ := hd
  refine ⟨fun a ha => by rw [mul_comm, mul_smul, h.1 a ha, smul_zero], fun b => ?_⟩
  obtain ⟨a, ha⟩ := h.2 (m • b)
  exact ⟨a, by rw [ha, mul_smul]⟩

theorem inv_of_field (l : ℕ) (k : Type) [Field k] (hl : IsUnit (l : k)) {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) : Inv l (sch.obj X) := by
  intro U ⟨x⟩
  have h := hl.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ ((show U ⟶ X from x) ≫ p).appTop).hom
  rwa [map_natCast] at h

theorem goal_of (hLH : LH) (hInv : SHInv) (hSt : Stalk) (hB : Bock) (hAd : AdicDeg) (hL : Limit) : GOAL := by
  intro a2 a6n a6r a7 a8 a9 a10 a11 b1 b2 b3 e2 e3 e4 l _ k _ _ hl X Y pX pY _ _ _ n i
  have hne : ∀ j : ℕ, NeZero (l ^ j) := fun j => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hu : ∀ j : ℕ, IsUnit ((l ^ j : ℕ) : k) := fun j => by rw [Nat.cast_pow]; exact hl.pow j
  have hA := hAd a11 l (sch.obj X) i (fun b => hB a7 a8 a10 a11 l b _ i (inv_of_field l k hl pX))
    (fun j m => e4 (l ^ j) k (hu j) pX m i)
  choose r c N hN hQ hI using hA
  obtain ⟨e, he⟩ := hLH a2 a6n b1
  let M : ℕ := n.toNat + 1
  let N' : ℕ := ∏ a ∈ Finset.range (M + 1), N (a : ℕ)
  have hN' : 0 < N' := Finset.prod_pos fun a _ => hN _
  refine hL a9 a11 l pX pY n i M (N' ^ e M) (fun a => r a) (fun a => c a) (by omega) (pow_pos hN' _) (fun a _ => hQ _)
    (fun j m => e4 (l ^ j) k (hu j) pY m 0) fun j => ?_
  refine he (l ^ j) pX (hu j) i _ _ M N' (fun A s hA m hm => ?_) pY n (by omega)
  exact hSt a6n a6r a9 b2 (l ^ j) pX A s hA (hu j) i _ _ M N' (hInv a9 b2 b3 e2 e3 (l ^ j) k (hu j) pX A s hA i)
    (fun a ha => (hI a j).comb_mono (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega)))) m hm

end LateralTheory.KummerTheory

end
end

-- bundled from Development.EtaleCohomology.KummerTheory.LimitPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.KummerTheory

def LimExtHl : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ),
  ∃ e : Hl l (sch.obj X) a i →ₗ[ℤ_[l]] Hl l (sch.obj Y) (n - a) 0 →ₗ[ℤ_[l]] Hl l (sch.obj (pullback pX pY)) n i,
    ∀ x y k, lev l (e x y) k = ext (l ^ k) pX pY a n i (lev l x k) (lev l y k)

def LimLH : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (n i : ℤ) (M N : ℕ)
  (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Hl l (sch.obj X) a i),
  (∀ (k : ℕ) (m : ℤ), Finite (Ht (l ^ k) (sch.obj Y) m 0)) →
  (∀ k, IsoUpTo N (lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n)) →
  ∃ Φ : (∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) →ₗ[ℤ_[l]]
      Hl l (sch.obj (pullback pX pY)) n i,
    (∀ y k, lev l (Φ y) k = lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y a s) k)) ∧
    IsoUpTo N Φ

def LimAssemble : Prop := A9 → ∀ (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (n i : ℤ) (M N : ℕ)
  (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Hl l (sch.obj X) a i), n ≤ M → 0 < N → (∀ a ≤ M, QBasis l (c a)) →
  ∀ (e : ∀ a : ℤ, Hl l (sch.obj X) a i →ₗ[ℤ_[l]] Hl l (sch.obj Y) (n - a) 0 →ₗ[ℤ_[l]] Hl l (sch.obj (pullback pX pY)) n i)
    (Φ : (∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) →ₗ[ℤ_[l]]
      Hl l (sch.obj (pullback pX pY)) n i),
  (∀ y, Φ y = ∑ a : Fin (M + 1), ∑ s : Fin (r a), e ((a : ℕ) : ℤ) (c a s) (y a s)) → IsoUpTo N Φ →
  ∃ κ : (⨁ a : ℤ, HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0) ≃ₗ[ℚ_[l]] HQ l (sch.obj (pullback pX pY)) n i,
    ∀ (a : ℤ) (x : Hl l (sch.obj X) a i) (y : Hl l (sch.obj Y) (n - a) 0),
      κ (DirectSum.lof ℚ_[l] ℤ (fun a : ℤ => HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0) a
        (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y))) = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] e a x y

theorem Limit_of (h1 : LimExtHl) (h2 : LimLH) (h3 : LimAssemble) : Limit := by
  intro hA9 hA11 l _ X Y S pX pY n i M N r c hnM hN hB hfin hiso
  choose e he using fun a : ℤ => h1 hA11 l pX pY a n i
  obtain ⟨Φ, hΦ, hΦN⟩ := h2 hA11 l pX pY n i M N r c hfin hiso
  have key : ∀ y, Φ y = ∑ a : Fin (M + 1), ∑ s : Fin (r a), e ((a : ℕ) : ℤ) (c a s) (y a s) := by
    intro y
    apply Subtype.ext
    funext k
    change lev l (Φ y) k = _
    rw [hΦ y k, Submodule.coe_sum, Finset.sum_apply]
    unfold lh
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact (he _ _ _ k).symm
  obtain ⟨κ, hκ⟩ := h3 hA9 l pX pY n i M N r c hnM hN hB e Φ key hΦN
  exact ⟨κ, fun a x y => ⟨e a x y, fun k => he a x y k, hκ a x y⟩⟩

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.PlacePf
section
noncomputable section
open GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def PlaceEx : Prop := ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K],
  ∃ (T : ValuationSubring K) (σ : k →+* T), (∀ x, (σ x : K) = algebraMap k K x) ∧
    Function.Surjective ((IsLocalRing.residue T).comp σ)

def ValAIC : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] (T : ValuationSubring K), AIC T ∧ HenselianLocalRing T

theorem Place_of (h1 : PlaceEx) (h2 : ValAIC) : Place := by
  intro k K _ _ _ _ _
  obtain ⟨T, σ, hσ, hs⟩ := h1 k K
  obtain ⟨hA, hH⟩ := h2 K T
  have hb : Function.Bijective ((IsLocalRing.residue T).comp σ) := ⟨RingHom.injective _, hs⟩
  refine ⟨T, σ, hσ, hb, hA, hH, ?_⟩
  have : IsAlgClosed (IsLocalRing.ResidueField T) := IsAlgClosed.of_ringEquiv k _ (RingEquiv.ofBijective _ hb)
  infer_instance

end LateralTheory.KummerTheory
end
end

