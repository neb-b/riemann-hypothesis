module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionLocalPresentationSmoothGroup
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AnalyticAtCoordinateZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ActOfGenerators
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.UnderMap

theorem sec_ext_of_pow_eq {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] [LocallyOfFiniteType G.hom]
    (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (u v : 𝟙_ (Over S) ⟶ G) (h : u ^ n = v ^ n)
    (hg : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      toUnit (Over.mk x) ≫ u = toUnit (Over.mk x) ≫ v) : u = v := by
  have hw : (Out.mulA G n).left ≫ G.hom = G.hom := Over.w _
  have h₁ : FormallyUnramified (Out.mulA G n).left := formallyUnramified_mulA S G n hn
  have h₂ : LocallyOfFiniteType ((Out.mulA G n).left ≫ G.hom) := by rw [hw]; infer_instance
  have h₃ : LocallyOfFiniteType (Out.mulA G n).left := locallyOfFiniteType_of_comp _ G.hom
  have e : ∀ w : 𝟙_ (Over S) ⟶ G, w ≫ Out.mulA G n = w ^ n := fun w => by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
  apply Over.OverMorphism.ext
  refine eq_of_range_equalizer_ι_eq_univ (Out.mulA G n).left
    (by rw [← Over.comp_left, ← Over.comp_left, e, e, h]) (Set.eq_univ_of_forall fun p => ?_)
  let k := AlgebraicClosure (S.residueField p)
  let x : Sp k ⟶ S := spMap (algebraMap (S.residueField p) k) ≫ S.fromSpecResidueField p
  have hx : x ≫ u.left = x ≫ v.left := by
    have := congrArg (fun z => z.left) (hg k x)
    simp only [Over.comp_left, ObjPull.toUnit_left'] at this
    exact this
  refine range_subset_range_equalizer_ι (T := S) x hx ⟨(default : PrimeSpectrum k), ?_⟩
  show S.fromSpecResidueField p _ = p
  exact Scheme.fromSpecResidueField_apply p _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem map_zero_of_add {A Q : Type} [AddGroup A] [Group Q] {F : A → Q} (h : ∀ a c, F (a + c) = F a * F c) :
    F 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem map_nsmul_of_add {A Q : Type} [AddGroup A] [Group Q] {F : A → Q} (h : ∀ a c, F (a + c) = F a * F c)
    (n : ℕ) (a : A) : F (n • a) = F a ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, map_zero_of_add h]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

def eqSub {A Q : Type} [AddGroup A] [Group Q] {F F' : A → Q} (h : ∀ a c, F (a + c) = F a * F c)
    (h' : ∀ a c, F' (a + c) = F' a * F' c) : AddSubgroup A :=
  AddMonoidHom.eqLocus (AddMonoidHom.mk' (fun a => Additive.ofMul (F a)) fun a c => congrArg Additive.ofMul (h a c))
    (AddMonoidHom.mk' (fun a => Additive.ofMul (F' a)) fun a c => congrArg Additive.ofMul (h' a c))

theorem mem_eqSub {A Q : Type} [AddGroup A] [Group Q] {F F' : A → Q} (h : ∀ a c, F (a + c) = F a * F c)
    (h' : ∀ a c, F' (a + c) = F' a * F' c) (a : A) : a ∈ eqSub h h' ↔ F a = F' a := Iff.rfl

theorem eta_eq_pow {B : Type} [CommRing B] {bB : Base l B} {S : Scheme.{0}} {sB : S ⟶ Sp B} (ob : Obj D l bB sB)
    (hd : l.M ∣ l.A) (a : D.La) (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)) :
    ob.eta a = ob.etaA a ^ (l.A / l.M) := by
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hq : 0 < l.A / l.M := Nat.div_pos (Nat.le_of_dvd l.A_pos hd) hM
  have hA : l.M * (l.A / l.M) = l.A := Nat.mul_div_cancel' hd
  have hp := ob.proper
  have hn : IsUnit (l.M : Γ(S, ⊤)) := by
    simpa using (bB.unit l.M hM).map (sB.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
  refine sec_ext_of_pow_eq ob.t.G l.M hn _ _ ?_ fun k _ _ x => ?_
  · rw [← pow_mul, mul_comm, hA, ← map_nsmul_of_add ob.etaA_add, ob.etaA_ker, ← map_nsmul_of_add ob.eta_add]
    apply ob.eta_ker
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    refine Submodule.smul_mem_smul ?_ trivial
    have hle : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb := Ideal.mul_le_left
    rw [l.prod] at hle
    exact hle (Ideal.mem_span_singleton_self _)
  · obtain ⟨β, hβ⟩ : ∃ β : B →+* k, x ≫ sB = spMap β := ⟨(Spec.preimage (x ≫ sB)).hom, (Spec.map_preimage _).symm⟩
    obtain ⟨-, I, -, h₁, h₂⟩ := ob.geom k x β hβ
    rw [h₂ a ha, MonObj.comp_pow, h₁ a, ← I.tower l.M (l.A / l.M) hM hq a, hA]

section Pull

variable {B B' : Type} [CommRing B] [CommRing B'] {bB : Base l B} {bB' : Base l B'} {S S' : Scheme.{0}}
  {sB : S ⟶ Sp B} {sB' : S' ⟶ Sp B'} {f : S' ⟶ S}

theorem eq_secPull {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (u' : 𝟙_ (Over S') ⟶ G') (u : 𝟙_ (Over S) ⟶ G) :
    u' = ObjPull.secPull h u ↔ u'.left ≫ φ = f ≫ u.left := by
  refine ⟨fun e => e ▸ ObjPull.secPull_left h u, fun e => ?_⟩
  apply Over.OverMorphism.ext
  apply h.1.hom_ext
  · rw [e, ObjPull.secPull_left]
  · rw [Over.w, Over.w]

theorem levels_of_basis (ob : Obj D l bB sB) (ob' : Obj D l bB' sB') (hd : l.M ∣ l.A) {n : ℕ}
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] D.La) {φ : ob'.t.G.left ⟶ ob.t.G.left} (h : IsGrpPullback ob'.t.G ob.t.G f φ)
    (hb : ∀ i, (ob'.etaA (bas (Pi.single i 1))).left ≫ φ = f ≫ (ob.etaA (bas (Pi.single i 1))).left) :
    (∀ a, (ob'.eta a).left ≫ φ = f ≫ (ob.eta a).left) ∧ ∀ a, (ob'.etaA a).left ≫ φ = f ≫ (ob.etaA a).left := by
  have hA : ∀ a, ob'.etaA a = ObjPull.secPull h (ob.etaA a) := by
    intro a
    have add : ∀ a c, ObjPull.secPull h (ob.etaA (a + c)) =
        ObjPull.secPull h (ob.etaA a) * ObjPull.secPull h (ob.etaA c) := fun a c => by rw [ob.etaA_add, map_mul]
    refine (mem_eqSub (F' := fun a => ObjPull.secPull h (ob.etaA a)) ob'.etaA_add add a).1 ?_
    obtain ⟨c, rfl⟩ := bas.surjective a
    have hc : c = ∑ i, c i • (Pi.single i 1 : Fin n → ℤ) := by
      ext j; simp [Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul]
    refine zsmul_mem ?_ _
    exact (eq_secPull h _ _).2 (hb i)
  refine ⟨fun a => (eq_secPull h _ _).1 ?_, fun a => (eq_secPull h _ _).1 (hA a)⟩
  have ha : a ∈ (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [l.coprime, Submodule.top_smul]; trivial
  rw [Submodule.sup_smul] at ha
  obtain ⟨a₁, h₁, a₂, h₂, rfl⟩ := Submodule.mem_sup.1 ha
  rw [ob.eta_add, ob'.eta_add, ob.eta_ker _ h₁, ob'.eta_ker _ h₁, _root_.one_mul, _root_.one_mul,
    eta_eq_pow ob hd _ h₂, eta_eq_pow ob' hd _ h₂, map_pow, hA]

theorem act_of_generators {O : Type} [CommRing O] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    (α : OAct O G) (α' : OAct O G') {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {J : Type} (a : J → O)
    (ha : Subring.closure (Set.range a) = ⊤)
    (hj : ∀ j, (α'.act (a j)).left ≫ φ = φ ≫ (α.act (a j)).left) (c : O) :
    (α'.act c).left ≫ φ = φ ≫ (α.act c).left := by
  have add' : ∀ a c, pushHom h G' (α'.act (a + c)) = pushHom h G' (α'.act a) * pushHom h G' (α'.act c) :=
    fun a c => by rw [α'.add, map_mul]
  have add : ∀ a c, pushHom h G' (𝟙 _) ≫ α.act (a + c) =
      (pushHom h G' (𝟙 _) ≫ α.act a) * (pushHom h G' (𝟙 _) ≫ α.act c) :=
    fun a c => by rw [α.add, MonObj.comp_mul]
  have key : ∀ c, c ∈ eqSub (F := fun c => pushHom h G' (α'.act c))
      (F' := fun c => pushHom h G' (𝟙 _) ≫ α.act c) add' add ↔ (α'.act c).left ≫ φ = φ ≫ (α.act c).left := fun c => by
    rw [mem_eqSub]
    have e : (pushHom h G' (𝟙 _) ≫ α.act c).left = φ ≫ (α.act c).left :=
      congrArg (· ≫ (α.act c).left) (Category.id_comp φ)
    exact ⟨fun H => (congrArg (fun z => z.left) H).trans e, fun H => Over.OverMorphism.ext (H.trans e.symm)⟩
  have hc : c ∈ Subring.closure (Set.range a) := by rw [ha]; trivial
  rw [← key]
  induction hc using Subring.closure_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact (key _).2 (hj j)
  | zero => exact zero_mem _
  | one => rw [key, α.one, α'.one]; simp
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx
  | mul x y _ _ hx hy =>
    rw [key] at hx hy ⊢
    rw [α.mul, α'.mul, Over.comp_left, Over.comp_left, Category.assoc, hy, reassoc_of% hx]

end Pull

theorem objMap_iff_tMap : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (l : Level H) (B o : Type) [CommRing B] [CommRing o] (bB : Base l B) (b : TBase o l.A) (S S' : Scheme.{0}) (sB : S ⟶ Sp B) (sB' : S' ⟶ Sp B) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (ob : Obj D l bB sB) (ob' : Obj D l bB sB') (t : TObj g l.A J b s) (t' : TObj g l.A J b s') (f : S' ⟶ S), l.M ∣ l.A → Subring.closure (Set.range a) = ⊤ → ObjUnder ob a bas t → ObjUnder ob' a bas t' → (Nonempty (ObjMap ob' ob f) ↔ TMap t' t f) := by
  intro hL _ E _ _ _ H D g J a bas l B o _ _ bB b S S' sB sB' s s' ob ob' t t' f hd ha
    ⟨e, he, heL, hea, hep⟩ ⟨e', he', heL', hea', hep'⟩
  have ih : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  have hi : e.hom.left ≫ e.inv.left = 𝟙 _ := by rw [← Over.comp_left, e.hom_inv_id, Over.id_left]
  have ih' : e'.inv.left ≫ e'.hom.left = 𝟙 _ := by rw [← Over.comp_left, e'.inv_hom_id, Over.id_left]
  have hi' : e'.hom.left ≫ e'.inv.left = 𝟙 _ := by rw [← Over.comp_left, e'.hom_inv_id, Over.id_left]
  have m₁ : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have m₂ : IsMonHom e'.symm.hom := inferInstanceAs (IsMonHom e'.inv)
  have a₁ : ∀ j, (ob.t.act.act (a j)).left ≫ e.hom.left = e.hom.left ≫ (t.act j).left := fun j =>
    congrArg (fun z => z.left) (hea j)
  have a₂ : ∀ j, (ob'.t.act.act (a j)).left ≫ e'.hom.left = e'.hom.left ≫ (t'.act j).left := fun j =>
    congrArg (fun z => z.left) (hea' j)
  have p₁ : ∀ i, (ob.etaA (bas (Pi.single i 1))).left ≫ e.hom.left = (t.pt i).left := hep
  have p₂ : ∀ i, (ob'.etaA (bas (Pi.single i 1))).left ≫ e'.hom.left = (t'.pt i).left := hep'
  constructor
  · rintro ⟨m⟩
    have mL : LBIso ob'.t.PP.L (ob.t.PP.L.pull m.cm.F) := by
      obtain ⟨w, hw, -⟩ := m.lin
      exact ⟨w, hw⟩
    refine ⟨e'.inv.left ≫ m.cm.F ≫ e.hom.left, ?_, ?_, fun i => ?_, fun j => ?_⟩
    · exact (IsGrpPullback.comp (isGrpPullback_of_iso e'.symm)
        (IsGrpPullback.comp m.cart (isGrpPullback_of_iso e))).congr (by simp) rfl
    · have k₁ : LBIso (ob'.t.PP.L.pull e'.inv.left) (t'.L.pull (𝟙 _)) := PELPull.lbIso_pull heL' e'.inv.left ih'.symm
      have k₂ : LBIso t'.L (ob'.t.PP.L.pull e'.inv.left) :=
        k₁.symm.chartPull (chartPullUnpull t'.L _ rfl) (chartPullId _)
      have k₃ : LBIso ob'.t.PP.L (t.L.pull (m.cm.F ≫ e.hom.left)) :=
        mL.trans ob'.t.PP.isLB (pull_isLB ob.t.PP.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull heL m.cm.F rfl)
      exact k₂.trans t'.isLB (pull_isLB ob'.t.PP.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull k₃ e'.inv.left rfl)
    · have := m.etaA (bas (Pi.single i 1))
      rw [← p₂, ← p₁, Category.assoc, reassoc_of% hi']
      exact (reassoc_of% this) _
    · have h₂ : (t'.act j).left ≫ e'.inv.left = e'.inv.left ≫ (ob'.t.act.act (a j)).left := by
        rw [← Category.id_comp (t'.act j).left, ← ih', Category.assoc, Category.assoc, ← reassoc_of% a₂ j, hi',
          Category.comp_id]
      have h₃ := m.act (a j)
      rw [reassoc_of% h₂, reassoc_of% h₃, a₁, Category.assoc, Category.assoc]
  · rintro ⟨ψ, hψ, hψL, hpt, hact⟩
    have hc : IsGrpPullback ob'.t.G ob.t.G f (e'.hom.left ≫ ψ ≫ e.inv.left) :=
      (IsGrpPullback.comp (isGrpPullback_of_iso e')
        (IsGrpPullback.comp hψ (isGrpPullback_of_iso e.symm))).congr (by simp) rfl
    have kL : LBIso ob'.t.PP.L (ob.t.PP.L.pull (e'.hom.left ≫ ψ ≫ e.inv.left)) := by
      have k₁ : LBIso ob'.t.PP.L (t.L.pull (e'.hom.left ≫ ψ)) :=
        heL'.trans ob'.t.PP.isLB (pull_isLB t'.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull hψL e'.hom.left rfl)
      refine k₁.trans ob'.t.PP.isLB (pull_isLB t.isLB _) (pull_isLB ob.t.PP.isLB _)
        (PELPull.lbIso_pull heL _ ?_).symm
      rw [Category.assoc, Category.assoc, ih, Category.comp_id]
    obtain ⟨m, hm⟩ := GlobalTheory.exists_sabMap_of_isProper_of_lbIso hL.globalFns E H S S' ob.t ob'.t f _ ob.proper hc kL
      (act_of_generators ob.t.act ob'.t.act hc a ha fun j => by
        have h₂ : (t.act j).left ≫ e.inv.left = e.inv.left ≫ (ob.t.act.act (a j)).left := by
          rw [← Category.id_comp (t.act j).left, ← ih, Category.assoc, Category.assoc, ← reassoc_of% a₁ j, hi,
            Category.comp_id]
        rw [reassoc_of% a₂ j, reassoc_of% hact j, h₂, Category.assoc, Category.assoc])
    obtain ⟨q₁, q₂⟩ := levels_of_basis ob ob' hd bas hc fun i => by
      have := hpt i
      rw [reassoc_of% p₂ i]
      refine ((reassoc_of% this) _).trans ?_
      rw [← p₁]
      exact congrArg (f ≫ ·) (by rw [Category.assoc, hi, Category.comp_id])
    rw [← hm] at q₁ q₂
    exact ⟨⟨m, q₁, q₂⟩⟩

end GlobalTheory.UnderMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAlgHomLocalizationAugmentation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_algHom_localization_augmentation (O : Type) [CommRing O] [IsLocalRing O]
    (H : Type) [CommRing H] [Algebra O H] (ε : H →ₐ[O] O) :
    ∃ εT : Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε) →ₐ[O] O,
      ∀ h, εT (algebraMap H _ h) = ε h := by

  have hunit : ∀ s : ((IsLocalRing.maximalIdeal O).comap ε).primeCompl, IsUnit (ε s) := by
    intro s
    by_contra hs
    apply s.2
    show ε s ∈ IsLocalRing.maximalIdeal O
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hs
  refine ⟨IsLocalization.liftAlgHom (M := ((IsLocalRing.maximalIdeal O).comap ε).primeCompl)
    (S := Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε)) hunit, fun h => ?_⟩
  rw [IsLocalization.liftAlgHom_apply]
  exact IsLocalization.lift_eq hunit h

theorem pow_dvd_trace_torsion :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] [Module.Free O H] (y : specO O H ⟶ G) (g : ℕ), SmoothOfRelativeDimension g G.hom → y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ h : H, (n : O) ^ g ∣ Algebra.trace O H h := by
  intro O _ _ G _ _ n H _ _ _ _ y g hsm hy huniv h

  obtain ⟨ε, hε, -⟩ := huniv O 1 (one_pow n)
  obtain ⟨εT, hεT⟩ := exists_algHom_localization_augmentation O H ε

  obtain ⟨S, _, _, π, x, a, ρ, hπ, hker, hkerε, ha, hρ, hρm⟩ :=
    _root_.GlobalTheory.TorsionPres.local_presentation O G n H y g hsm hy huniv ε hε
      (Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε)) εT hεT

  obtain ⟨l, hl, hdvd, hlm⟩ :=
    _root_.GlobalTheory.exists_integral_of_local_presentation O H ε g n (Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε)) εT hεT
      S π x a ρ hπ hker hkerε ha hρ hρm

  obtain ⟨Θ, hΘ⟩ := _root_.GlobalTheory.TorsionTheta.exists_theta O G n H y hy huniv ε l (ε l) hε hl rfl hlm
  exact dvd_trans hdvd (_root_.GlobalTheory.dvd_trace_of_balanced_tensor O H Θ (ε l) hΘ h)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELOfTmap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem GlobalTheory.exists_isPEL_of_tmap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (t : TObj g k J b s) (t' : TObj g k J b s') (τ : SAB H S) (f : S' ⟶ S), f ≫ s = s' → TMap t' t f → IsPEL D a bas ρ t τ → ∃ τ' : SAB H S', IsPEL D a bas ρ t' τ' := by
  intro E _ _ _ H D g J a bas k o _ b ρ S S' s s' t t' τ f hs ht hP

  exact GlobalTheory.PELPull.isPEL_pull E H D g k J a bas o b ρ S S' s s' f t t' τ hs ht hP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRelativeExpOfParts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology

noncomputable section

namespace GlobalTheory.RelExp

theorem exists_lift {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m n : ℕ} {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)}
    {U : G.left.Opens} {t : Fin g → Γ(G.left, U)} {f : Fin n → Γ(G.left, U)} {O : Set ((Fin m → ℂ) × (Fin n → ℂ))}
    {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} {Q : Set ((Fin m → ℂ) × (Fin g → ℂ))}
    {L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)} (hO : IsOpen O) (hQ : IsOpen Q)
    (hadd : ∀ b z w, e b (z + w) = e b z * e b w)
    (hinv : ∀ b (a : Over.mk (y b) ⟶ G), ⊤ ≤ pt a ⁻¹ᵁ U → (b, crd U f (pt a)) ∈ O → (b, crd0 t a) ∈ Q →
      e b (L (b, crd0 t a)) = a)
    {k : ℕ} {β : (Fin k → ℂ) → (Fin m → ℂ)} {x : ∀ w, Over.mk (y (β w)) ⟶ G} {w₀ : Fin k → ℂ} {z₀ : Fin g → ℂ}
    (hβ : AnalyticAt ℂ β w₀) (hx : HolAt (fun w => pt (x w)) w₀) (h0 : e (β w₀) z₀ = x w₀)
    (he : HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (e q.1 q.2)) (β w₀, z₀))
    (hU : ⊤ ≤ pt (1 : Over.mk (y (β w₀)) ⟶ G) ⁻¹ᵁ U) (hO₀ : (β w₀, crd U f (pt (1 : Over.mk (y (β w₀)) ⟶ G))) ∈ O)
    (hQ₀ : (β w₀, 0) ∈ Q) (hL0 : L (β w₀, 0) = 0) (hL : AnalyticAt ℂ L (β w₀, 0)) :
    ∃ ζ : (Fin k → ℂ) → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in 𝓝 w₀, e (β w) (ζ w) = x w := by
  have h1 := HolAt.comp (φ := fun w => (β w, z₀)) (v₀ := w₀) he (hβ.prod analyticAt_const)
  have h2 := HolAt.inv (y := fun w => y (β w)) (a := fun w => e (β w) z₀) h1
  have ha : HolAt (fun w => pt (x w * (e (β w) z₀)⁻¹)) w₀ :=
    HolAt.mul (y := fun w => y (β w)) (a := x) (b := fun w => (e (β w) z₀)⁻¹) hx h2
  have ha0 : x w₀ * (e (β w₀) z₀)⁻¹ = 1 := by rw [h0, mul_inv_cancel]
  have hc : AnalyticAt ℂ (fun w => (β w, crd0 t (x w * (e (β w) z₀)⁻¹))) w₀ :=
    hβ.prod (HolAt.analyticAt_coordinate_zero (a := fun w => x w * (e (β w) z₀)⁻¹) ha ha0 hU)
  have hc0 : (β w₀, crd0 t (x w₀ * (e (β w₀) z₀)⁻¹)) = (β w₀, 0) := by
    rw [ha0]; exact Prod.ext rfl (sub_self _)
  refine ⟨fun w => L (β w, crd0 t (x w * (e (β w) z₀)⁻¹)) + z₀, ?_, ?_, ?_⟩
  · simp only [hc0, hL0, zero_add]
  · exact (AnalyticAt.comp (g := L) (hc0 ▸ hL) hc).add analyticAt_const
  · filter_upwards [HolAt.eventually_near (a := fun w => x w * (e (β w) z₀)⁻¹) ha hβ.continuousAt ha0 hO hU hO₀,
      hc.continuousAt.eventually (hQ.mem_nhds (by simpa only [hc0] using hQ₀))] with w h3 h4
    rw [hadd, hinv _ _ h3.1 h3.2 h4, inv_mul_cancel_right]

theorem exists_relative_exp_of_parts
    (hchart : ∀ (m g : ℕ) (Z X : Scheme.{0}) (p : Z ⟶ X) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (z₀ : Sp ℂ ⟶ Z), SmoothOfRelativeDimension g p → IsOpen B → b₀ ∈ B → IsHolTo B y → z₀ ≫ p = y b₀ → ∃ (U : Z.Opens) (t : Fin g → Γ(Z, U)) (n : ℕ) (f : Fin n → Γ(Z, U)) (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ Z)), IsOpen N ∧ IsOpen O ∧ ⊤ ≤ z₀ ⁻¹ᵁ U ∧ (b₀, fun j => valAt' z₀ U (f j)) ∈ O ∧ IsHolTo N σ ∧ (∀ q ∈ N, σ q ≫ p = y q.1 ∧ ⊤ ≤ σ q ⁻¹ᵁ U ∧ ∀ i, valAt' (σ q) U (t i) = q.2 i) ∧ (∀ (b : Fin m → ℂ) (x : Sp ℂ ⟶ Z), x ≫ p = y b → ⊤ ≤ x ⁻¹ᵁ U → (b, fun j => valAt' x U (f j)) ∈ O → (b, fun i => valAt' x U (t i)) ∈ N ∧ σ (b, fun i => valAt' x U (t i)) = x) ∧ ∀ (v v' : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ p = v' ≫ p → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v')
    (htan : ∀ (X : Scheme.{0}) (G : Over X) (x : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk x ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) → (∀ w, ∃! v : epsPt x ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ ∀ (U : G.left.Opens) (t : Fin g → Γ(G.left, U)), ⊤ ≤ (show Sp ℂ ⟶ G.left from (e 0).left) ⁻¹ᵁ U → (∀ (v v' : Sp (DualNumber ℂ) ⟶ G.left) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ G.hom = v' ≫ G.hom → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v') → ((∀ v : epsPt x ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) ↔ Function.Injective (fderiv ℂ (fun z i => valAt' (e z).left U (t i)) 0)))
    (hexp : ∀ (m g : ℕ) (b₀ : Fin m → ℂ) (M : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ M (b₀, 0, 0) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), M (q.1, q.2, 0) = q.2) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), M (q.1, q.2.1, q.2.2) = M (q.1, q.2.2, q.2.1)) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0, 0), M (q.1, M (q.1, q.2.1, q.2.2.1), q.2.2.2) = M (q.1, q.2.1, M (q.1, q.2.2.1, q.2.2.2))) → ∃ E L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in nhds b₀, E (b, 0) = 0 ∧ HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧ ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), E (q.1, q.2.1 + q.2.2) = M (q.1, E (q.1, q.2.1), E (q.1, q.2.2)))
    (hsub : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (x : Sp ℂ ⟶ X) (H : Subgroup (Over.mk x ⟶ G)) (U : G.left.Opens) (κ : Type) [Fintype κ] (f : κ → Γ(G.left, U)) (O : Set (κ → ℂ)), Smooth G.hom → GeometricallyConnected G.hom → IsOpen O → ⊤ ≤ (show Sp ℂ ⟶ G.left from (1 : Over.mk x ⟶ G).left) ⁻¹ᵁ U → (fun j => valAt' (1 : Over.mk x ⟶ G).left U (f j)) ∈ O → (∀ a : Over.mk x ⟶ G, ⊤ ≤ (show Sp ℂ ⟶ G.left from a.left) ⁻¹ᵁ U → (fun j => valAt' a.left U (f j)) ∈ O → a ∈ H) → H = ⊤) :
    ∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (G : Over X) [GrpObj G] (g m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶ G)), LocallyOfFiniteType s → IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ((∀ z w, e₀ (z + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀ ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧ (∀ w, ∃! v : epsPt (y b₀) ⟶ G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y b₀) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀ 0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) → ∃ (B' : Set (Fin m → ℂ)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (r : ℝ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ e b₀ = e₀ ∧ 0 < r ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ (∀ b ∈ B', ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) ∧ ∀ (n : ℕ) (W : Set (Fin n → ℂ)) (β : (Fin n → ℂ) → (Fin m → ℂ)) (x : ∀ w, Over.mk (y (β w)) ⟶ G) (w₀ : Fin n → ℂ) (z₀ : Fin g → ℂ), IsOpen W → w₀ ∈ W → DifferentiableOn ℂ β W → Set.MapsTo β W B' → IsHolTo W (fun w => (x w).left) → e (β w₀) z₀ = x w₀ → ∃ ζ : (Fin n → ℂ) → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w := by
  intro k _ σ₀ X s₀ G _ g m B y b₀ e₀ _ hab hsm hB hb₀ _ hy ⟨he₀add, _, he₀hol, _, he₀tan⟩
  have := hab.comm
  have hy₀ : HolAt y b₀ := ⟨B, hB, hb₀, hy⟩
  obtain ⟨U, t, n, f, N, O, σ, hN, hO, hU, hO₀, hσ, hσN, hσinv, hunr⟩ :=
    hchart m g G.left X G.hom B y b₀ (pt (1 : Over.mk (y b₀) ⟶ G)) hsm hB hb₀ hy (Over.w _)
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_centred_chart hy₀ hN hU hO₀ hσ hσN hσinv
  obtain ⟨B', e, r, Q, L, hB', hb', hB'B, hr, hQ, hadd, hfib, hinv⟩ :=
    exists_global_exp hexp (hB.mem_nhds hb₀) hy₀ hO hU hO₀ hs1 hs2 hs3
  have hzero : ∀ {x : Sp ℂ ⟶ X} {u : (Fin g → ℂ) → (Over.mk x ⟶ G)}, (∀ z w, u (z + w) = u z * u w) → u 0 = 1 :=
    fun {x u} h => by
      have := h 0 0
      rw [add_zero] at this
      exact mul_eq_left.1 this.symm
  have he₀0 : e₀ 0 = 1 := hzero he₀add
  have he₀U : ⊤ ≤ pt (e₀ 0) ⁻¹ᵁ U := by rw [he₀0]; exact hU
  have hinj := ((htan X G (y b₀) g e₀ he₀hol).2 U t he₀U hunr).1 he₀tan
  set T₀ : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := fderiv ℂ (fun z => crd U t (pt (e₀ z))) 0 with hT₀
  have hsurj : Function.Surjective T₀ :=
    (LinearMap.injective_iff_surjective (f := (T₀ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)))).1 hinj
  let T : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) := ContinuousLinearEquiv.ofBijective T₀ (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj)
  have hT : ∀ z, T z = T₀ z := fun _ => rfl
  have hhol : ∀ b ∈ B', ∀ z, HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (e q.1 (T₀ q.2))) (b, z) :=
    fun b hb z => by
      have := HolAt.comp (φ := fun q : (Fin m → ℂ) × (Fin g → ℂ) => (q.1, T₀ q.2)) (v₀ := (b, z))
        ((hfib b hb).1 (T₀ z)) (analyticAt_fst.prod ((T₀.analyticAt _).comp analyticAt_snd))
      exact this
  refine ⟨B', fun b z => e b (T₀ z), r / (‖T₀‖ + 1), hB', hb', hB'B, ?_, by positivity,
    isHolTo_of_holAt (hB'.prod isOpen_univ) fun q hq => hhol q.1 hq.1 q.2, fun b hb => ?_, ?_⟩
  ·
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hfib b₀ hb'
    obtain ⟨ζ, hζ0, hζ, hζe⟩ := exists_lift hO hQ hadd hinv (β := fun _ : Fin g → ℂ => b₀) (x := e₀) (w₀ := 0)
      (z₀ := 0) analyticAt_const ⟨Set.univ, isOpen_univ, trivial, he₀hol⟩ ((hzero (hadd b₀)).trans he₀0.symm)
      (h1 0) h2 h3 h4 h6 h7
    have hd : HasFDerivAt ζ T₀ 0 := by
      have k1 := HasFDerivAt.comp (f := ζ) (0 : Fin g → ℂ) (hζ0.symm ▸ h5) hζ.differentiableAt.hasFDerivAt
      have k2 : HasFDerivAt (fun z => crd U t (pt (e₀ z))) _ 0 := k1.congr_of_eventuallyEq
        (hζe.mono fun z hz => by simp only [Function.comp, hz])
      rw [hT₀, k2.fderiv, ContinuousLinearMap.id_comp]
      exact hζ.differentiableAt.hasFDerivAt
    have tζ : Tendsto ζ (𝓝 0) (𝓝 0) := by simpa only [ContinuousAt, hζ0] using hζ.continuousAt
    have t1 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => p.1) (𝓝 0) (𝓝 0) := continuous_fst.tendsto 0
    have t2 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => p.2) (𝓝 0) (𝓝 0) := continuous_snd.tendsto 0
    have t3 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => p.1 + p.2) (𝓝 0) (𝓝 0) := by simpa using t1.add t2
    have t4 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => ζ (p.1 + p.2) - (ζ p.1 + ζ p.2)) (𝓝 0) (𝓝 0) := by
      simpa using (tζ.comp t3).sub ((tζ.comp t1).add (tζ.comp t2))
    have hζT := eventuallyEq_of_additive_of_hasFDerivAt hd (by
      filter_upwards [t1.eventually hζe, t2.eventually hζe, t3.eventually hζe,
        t4.eventually (Metric.ball_mem_nhds 0 hr)] with p k1 k2 k3 k4
      refine sub_eq_zero.1 (h8 _ (mem_ball_zero_iff.1 k4) ?_)
      have k5 := hadd b₀ (ζ (p.1 + p.2) - (ζ p.1 + ζ p.2)) (ζ p.1 + ζ p.2)
      rw [sub_add_cancel, hadd b₀ (ζ p.1), k1, k2, k3, he₀add] at k5
      exact mul_eq_right.1 k5.symm)
    have key := addMonoidHom_eq_of_eventuallyEq
      (e := AddMonoidHom.mk' (fun z => Additive.ofMul (e b₀ (T₀ z))) fun z w => by rw [map_add (f := _), hadd]; rfl)
      (e' := AddMonoidHom.mk' (fun z => Additive.ofMul (e₀ z)) fun z w => by rw [he₀add]; rfl) (by
        filter_upwards [hζT, hζe] with z k1 k2
        exact congrArg Additive.ofMul (by rw [← k1]; exact k2))
    exact funext fun z => congrArg Additive.toMul (DFunLike.congr_fun key z)
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hfib b hb
    have hH : IsHolTo Set.univ (fun z => pt (e b (T₀ z))) := isHolTo_of_holAt isOpen_univ fun z _ => by
      have := HolAt.comp (φ := fun z : Fin g → ℂ => (b, z)) (v₀ := z) (hhol b hb z)
        (analyticAt_const.prod analyticAt_id)
      exact this
    have hadd' : ∀ z w, e b (T₀ (z + w)) = e b (T₀ z) * e b (T₀ w) := fun z w => by rw [map_add (f := _), hadd]
    obtain ⟨k1, k2⟩ := htan X G (y b) g (fun z => e b (T₀ z)) hH
    refine ⟨⟨hadd', ?_, hH, k1, (k2 U t ?_ hunr).2 ?_⟩, fun z hz h => ?_⟩
    · refine Function.Surjective.comp (g := e b) ?_ hsurj
      let ε : (Fin g → ℂ) →+ Additive (Over.mk (y b) ⟶ G) :=
        AddMonoidHom.mk' (fun z => Additive.ofMul (e b z)) fun z w => by rw [hadd]; rfl
      have hc : Continuous fun u : Fin n ⊕ Fin g → ℂ => (b, fun j => u (Sum.inl j)) := by fun_prop
      have hc' : Continuous fun u : Fin n ⊕ Fin g → ℂ =>
        (b, (fun j => u (Sum.inr j)) - crd U t (pt (1 : Over.mk (y b) ⟶ G))) := by fun_prop
      have := hsub X G (y b) (AddSubgroup.toSubgroup' ε.range) U (Fin n ⊕ Fin g) (Sum.elim f t) _ hab.smooth
        hab.geomConnected ((hO.preimage hc).inter (hQ.preimage hc')) h2
        ⟨h3, by simpa only [Set.mem_preimage, Sum.elim_inr, sub_self] using h4⟩
        fun a ha hb => ⟨_, congrArg Additive.ofMul (hinv b a ha hb.1 hb.2)⟩
      intro a
      obtain ⟨z, hz⟩ : a ∈ AddSubgroup.toSubgroup' ε.range := this ▸ Subgroup.mem_top a
      exact ⟨z, congrArg Additive.toMul hz⟩
    · rw [hzero (u := fun z => e b (T₀ z)) hadd']; exact h2
    · have := HasFDerivAt.comp (f := T₀) (0 : Fin g → ℂ) (by rw [map_zero]; exact h5) T₀.hasFDerivAt
      have k3 : fderiv ℂ (fun z => crd U t (pt (e b (T₀ z)))) 0 = _ := this.fderiv
      rw [ContinuousLinearMap.id_comp] at k3
      exact k3.symm ▸ hinj
    · refine hinj ((h8 _ ((T₀.le_opNorm z).trans_lt ?_) h).trans (map_zero T₀).symm)
      rw [lt_div_iff₀ (by positivity)] at hz
      nlinarith [norm_nonneg z]
  · intro j W β x w₀ z₀ hW hw₀ hβ hβW hx h0
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hfib _ (hβW hw₀)
    obtain ⟨ζ, hζ0, hζ, hζe⟩ := exists_lift hO hQ hadd hinv (x := x)
      (SCV.analyticAt_of_differentiableOn hβ (hW.mem_nhds hw₀)) ⟨W, hW, hw₀, hx⟩ h0 (h1 _) h2 h3 h4 h6 h7
    refine ⟨fun w => T.symm (ζ w), by simp only [hζ0, ← hT, T.symm_apply_apply], (T.symm.analyticAt _).comp hζ, ?_⟩
    filter_upwards [hζe] with w hw
    rw [← hT, T.apply_symm_apply, hw]

theorem exists_relative_exp :
    ∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (G : Over X) [GrpObj G] (g m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶ G)), LocallyOfFiniteType s → IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ((∀ z w, e₀ (z + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀ ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧ (∀ w, ∃! v : epsPt (y b₀) ⟶ G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y b₀) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀ 0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) → ∃ (B' : Set (Fin m → ℂ)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (r : ℝ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ e b₀ = e₀ ∧ 0 < r ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ (∀ b ∈ B', ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) ∧ ∀ (n : ℕ) (W : Set (Fin n → ℂ)) (β : (Fin n → ℂ) → (Fin m → ℂ)) (x : ∀ w, Over.mk (y (β w)) ⟶ G) (w₀ : Fin n → ℂ) (z₀ : Fin g → ℂ), IsOpen W → w₀ ∈ W → DifferentiableOn ℂ β W → Set.MapsTo β W B' → IsHolTo W (fun w => (x w).left) → e (β w₀) z₀ = x w₀ → ∃ ζ : (Fin n → ℂ) → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w :=
  exists_relative_exp_of_parts (RelChart.exists_chart_with_parameters EtaleFamily.exists_holomorphic_sections)
    vertical_derivative_in_coordinates exists_param_exp_log_pi OpenSubgroupPts.subgroup_eq_top_of_nhds_one

end GlobalTheory.RelExp
end
end

