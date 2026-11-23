module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainDegreeZeroSubsingleton
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0102
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0101
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompShiftZero

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FBnat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

theorem CrystallineSemistableComparison.B.P.bnat : ∀ {R : Type} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M] (N : SingleObj (Multiplicative ℕ) ⥤ ModuleCat.{w} R) (a : M →ₗ[R] N.obj (SingleObj.star _)) (s : R), (∀ x, (N.map (X := SingleObj.star _) (Y := SingleObj.star _) (Multiplicative.ofAdd 1)).hom (a x) = a x) → Acyc1 s a (N.map (X := SingleObj.star _) (Y := SingleObj.star _) (Multiplicative.ofAdd 1)).hom → (cx N).ResUpTo s (aug N fun _ => a) := fun N a s h H =>
  GlobalTheory.CompanionTheory.NatCoh.resUpTo_of_acyc N a s h H.1 (fun y hy => H.2.1 y (sub_eq_zero.1 hy)) H.2.2
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FLineUniv
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

theorem CrystallineSemistableComparison.B.P.line_univ : ∀ {C : Type u} [Category.{v} C] (U : UF C) (P : ∀ ⦃T T' : C⦄, (T ⟶ T') → (T' ⟶ T') → Prop), (∀ T : C, ∃ (T₁ : C) (i : T ⟶ T₁) (η : U.U T₁), (∀ (T' : C) (φ : T ⟶ T') (a : U.U T'), ∃! ψ : T₁ ⟶ T', i ≫ ψ = φ ∧ U.map ψ η = a) ∧ ∀ g : T₁ ⟶ T₁, i ≫ g = i → U.map g η = U.q _ * η → P i g) → ∃ L : Line (𝟭 C) U, ∀ T, P (L.i.app T) (L.γ.app T) :=
  @GlobalTheory.CompanionTheory.LineUniv.exists_line
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FNiCoh
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

section NiCoh

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

theorem ni_nat {F F' : C ⥤ ModuleCat.{w} R} (β : F ⟶ F') {T T' : C} (φ : T ⟶ T') (x : F.obj T) :
    (β.app T').hom ((F.map φ).hom x) = (F'.map φ).hom ((β.app T).hom x) := by
  rw [← ModuleCat.comp_apply, β.naturality, ModuleCat.comp_apply]

theorem ni_pull_cls {F F' : C ⥤ ModuleCat.{w} R} (β : F ⟶ F') (n : ℕ) (a : Cn F n) (ha : d F n a = 0) :
    ∃ hb, (Mor.ofNatTrans β).pull n ((cx F).cls a ha) = (cx F').cls (fun s => (β.app _).hom (a s)) hb := by
  have hb : d F' n (fun s => (β.app _).hom (a s)) = 0 :=
    ((Mor.ofNatTrans β).d_pullC n a).trans (by rw [ha, map_zero])
  exact ⟨hb, CrystallineSemistableComparison.P.mapH_cls (Mor.ofNatTrans β).hom n a ha hb⟩

theorem ni_pull_add {F F' : C ⥤ ModuleCat.{w} R} (β β' : F ⟶ F') (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (β + β')).pull n x = (Mor.ofNatTrans β).pull n x + (Mor.ofNatTrans β').pull n x := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (β + β') n a ha
  obtain ⟨h2, e2⟩ := ni_pull_cls β n a ha
  obtain ⟨h3, e3⟩ := ni_pull_cls β' n a ha
  rw [e1, e2, e3, ← (CrystallineSemistableComparison.P.cls_surj (cx F') n).2.2.2.1 _ _ h2 h3 (by rw [map_add (f := _), h2, h3, add_zero])]
  congr 1

theorem ni_pull_zero {F F' : C ⥤ ModuleCat.{w} R} (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (0 : F ⟶ F')).pull n x = 0 := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (0 : F ⟶ F') n a ha
  rw [e1, (CrystallineSemistableComparison.P.cls_surj (cx F') n).2.1]
  have : (fun s => ((0 : F ⟶ F').app _).hom (a s)) = (0 : Cn F' n) := by
    funext s
    simp only [NatTrans.app_zero, ModuleCat.hom_zero, LinearMap.zero_apply, Pi.zero_apply]
  rw [this]
  exact Submodule.zero_mem _

theorem ni_pull_sum {ι : Type} {F F' : C ⥤ ModuleCat.{w} R} (β : ι → (F ⟶ F')) (S : Finset ι) (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (∑ k ∈ S, β k)).pull n x = ∑ k ∈ S, (Mor.ofNatTrans (β k)).pull n x := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ni_pull_zero]
  | insert k S hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, ni_pull_add, ih]

theorem ni_pull_comp {F F' F'' : C ⥤ ModuleCat.{w} R} (β : F ⟶ F') (β' : F' ⟶ F'') (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (β ≫ β')).pull n x = (Mor.ofNatTrans β').pull n ((Mor.ofNatTrans β).pull n x) := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (β ≫ β') n a ha
  obtain ⟨h2, e2⟩ := ni_pull_cls β n a ha
  obtain ⟨h3, e3⟩ := ni_pull_cls β' n _ h2
  rw [e1, e2, e3]
  rfl

theorem ni_pull_id {F : C ⥤ ModuleCat.{w} R} (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (𝟙 F)).pull n x = x := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (𝟙 F) n a ha
  rw [e1]
  rfl

def fixF {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) : SubF F where
  S T := LinearMap.ker ((e.app T).hom - LinearMap.id)
  map_mem := fun {_ _} φ {_} hx => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
    rw [ni_nat, hx]

theorem mem_fixF {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) (T : C) (x : F.obj T) :
    x ∈ (fixF e).S T ↔ (e.app T).hom x = x := by
  change x ∈ LinearMap.ker ((e.app T).hom - LinearMap.id) ↔ _
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

def fixP {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) (he : e ≫ e = e) : F ⟶ (fixF e).fn where
  app T := ModuleCat.ofHom (LinearMap.codRestrict _ (e.app T).hom fun x => by
    rw [mem_fixF, ← ModuleCat.comp_apply, ← NatTrans.comp_app, he])
  naturality T T' φ := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (ni_nat e φ x))

def fixI {F : C ⥤ ModuleCat.{w} R} (S : SubF F) : S.fn ⟶ F where
  app T := ModuleCat.ofHom (S.S T).subtype
  naturality _ _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

theorem fixP_fixI {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) (he : e ≫ e = e) : fixP e he ≫ fixI (fixF e) = e :=
  NatTrans.ext (funext fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

def gNat {d : ℕ} (G : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (g : Gam d) : G ⟶ G where
  app _ := G.map (X := SingleObj.star _) (Y := SingleObj.star _) g
  naturality X Y a := by
    rw [← G.map_comp, ← G.map_comp]
    congr 1
    exact mul_comm (g : Gam d) (a : Gam d)

theorem gNat_pull {d : ℕ} (G : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (g : Gam d) (n : ℕ) (x : H G n) :
    (Mor.ofNatTrans (gNat G g)).pull n x = x := by
  have := CrystallineSemistableComparison.P.prism (Mor.ofNatTrans (gNat G g)) (Mor.id G)
    { app := fun _ => (g : SingleObj.star (Gam d) ⟶ SingleObj.star (Gam d)), naturality := fun _ _ a => mul_comm (g : Gam d) (a : Gam d) }
    (fun T x => rfl) n x
  rw [this]
  exact ((CrystallineSemistableComparison.P.pull_comp (Mor.id G) (Mor.id G) n x).2)

theorem killed_of {d : ℕ} (G : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (g : Gam d) (s : R)
    (hu : ∀ T, UpTo s ((gNat G g - 𝟙 G).app T).hom) (n : ℕ) (z : H G n) : s ^ 2 • z = 0 := by
  obtain ⟨x, hx⟩ := (CrystallineSemistableComparison.P.coef_upTo _ s hu n).2 z
  rw [← hx]
  have e1 := ni_pull_add (gNat G g - 𝟙 G) (𝟙 G) n x
  rw [sub_add_cancel, gNat_pull, ni_pull_id] at e1
  calc _ = ((Mor.ofNatTrans (gNat G g - 𝟙 G)).pull n x + x) - x := (add_sub_cancel_right _ _).symm
    _ = x - x := by rw [← e1]
    _ = 0 := sub_self x

theorem ni_killed {d : ℕ} (s : R) {M N : SingleObj (Gam d) ⥤ ModuleCat.{w} R} (α : M ⟶ N) (h : NI s α) (k : Fin d)
    (n : ℕ) (z : H (fixF (h.π k)).fn n) : s ^ 2 • z = 0 := by
  refine killed_of _ (gen k) s (fun T => ?_) n z
  change UpTo s ((gNat (fixF (h.π k)).fn (gen k) - 𝟙 _).app (SingleObj.star _)).hom
  have hδ : ∀ y : (fixF (h.π k)).fn.obj (SingleObj.star _), ((gNat (fixF (h.π k)).fn (gen k) - 𝟙 _).app (SingleObj.star _)).hom y =
      ((fixF (h.π k)).fn.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen k)).hom y - y := fun y => rfl
  refine ⟨fun y hy => ?_, fun y => ?_⟩
  · rw [hδ, sub_eq_zero] at hy
    have h1 : ((h.π k).app _).hom y.1 = y.1 := (mem_fixF (h.π k) _ y.1).1 y.2
    exact Subtype.ext (h.inj k y.1 h1 (congrArg Subtype.val hy))
  · have h1 : ((h.π k).app _).hom y.1 = y.1 := (mem_fixF (h.π k) _ y.1).1 y.2
    obtain ⟨x, hx, hx2⟩ := h.surj k y.1 h1
    exact ⟨⟨x, (mem_fixF (h.π k) _ x).2 hx⟩, by rw [hδ]; exact Subtype.ext hx2⟩

end NiCoh

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.ni_coh : ∀ {R : Type} [CommRing R] {d : ℕ} (s : R) {M N : SingleObj (Gam d) ⥤ ModuleCat.{w} R} (α : M ⟶ N), NI s α → ∀ n, IsoLe (s ^ 2) n (Mor.ofNatTrans α) := by
  intro R _ d s M N α h n j _
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · have e := ni_pull_comp α h.ρ j x
    rw [h.αρ, ni_pull_id, hx, map_zero] at e
    rw [e, smul_zero]
  · refine ⟨(Mor.ofNatTrans h.ρ).pull j (s ^ 2 • y), ?_⟩
    rw [← ni_pull_comp]
    have e := ni_pull_add (h.ρ ≫ α) (∑ k, h.π k) j (s ^ 2 • y)
    rw [h.sum, ni_pull_id, ni_pull_sum] at e
    have hk : ∀ k, (Mor.ofNatTrans (h.π k)).pull j (s ^ 2 • y) = 0 := by
      intro k
      rw [← fixP_fixI (h.π k) (h.idem k), ni_pull_comp, map_smul, ni_killed s α h k, map_zero]
    rw [Finset.sum_eq_zero (fun k _ => hk k), add_zero] at e
    exact e.symm
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FReesDown
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

theorem CrystallineSemistableComparison.B.P.rees_down : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F) (G : C' ⥤ C) (n N : ℕ), (∀ T, (Φ.S 0).S T = ⊤) → RI ((X : ℤ[X]) ^ N) n Φ.rees G → ∀ j ≤ n, InjUpTo (Φ.μ ^ N) ((Mor.restrict F G).pull j) ∧ ∀ y, ∃ x ∈ (Φ.S N).img j, (Mor.restrict F G).pull j x = Φ.μ ^ N • y :=
  @GlobalTheory.CompanionTheory.ReesDown.main
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FReesUp
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

theorem CrystallineSemistableComparison.B.P.rees_up : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F) (G : C' ⥤ C) (n : ℕ), ((∀ r, RI 1 n (Φ.S r).fn G) → RI 1 n Φ.rees G) ∧ (∀ μ' ξ : R, Φ.μ = μ' * ξ → (∀ r T x, x ∈ (Φ.S r).S T → ξ • x ∈ (Φ.S (r + 1)).S T) → (∀ r, Desc μ' (Φ.S r).fn G) → Desc (X : ℤ[X]) Φ.rees G) ∧ ∀ {T T' : C} (i : T ⟶ T') (g : T' ⟶ T'), Φ.FAcyc i g → Acyc1 (X : ℤ[X]) (Φ.rees.map i).hom (Φ.rees.map g).hom :=
  @GlobalTheory.CompanionTheory.ReesUp.main
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FResLe
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

theorem resLe_cls_zero {R : Type} [CommRing R] (K : Cx.{w} R) (n : ℕ) (a : K.X n) (ha : K.d n a = 0)
    (h : a ∈ K.B n) : K.cls a ha = 0 := ((CrystallineSemistableComparison.P.cls_surj K n).2.1 a ha).2 h

theorem resLe_cls_smul {R : Type} [CommRing R] (K : Cx.{w} R) (n : ℕ) (r : R) (a : K.X n) (ha : K.d n a = 0)
    (hb : K.d n (r • a) = 0) : K.cls (r • a) hb = r • K.cls a ha := (CrystallineSemistableComparison.P.cls_surj K n).2.2.2.2 r a ha hb

theorem eq_zero_of_mem_boundaries_zero {R : Type} [CommRing R] (K : Cx.{w} R) (a : K.X 0) (h : a ∈ K.B 0) : a = 0 :=
  (Submodule.mem_bot R).1 h

theorem resLe_succ {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R))
    (n : ℕ) (hK : ExactUpTo (1 : R) (K.d n) (K.d (n + 1))) (s : R) :
    UpTo s (φ.mapH (n + 1)) ↔ ExactUpTo s (L.d n) (L.d (n + 1)) := by
  have hz : ∀ x : K.H (n + 1), x = 0 := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K (n + 1)).1 x
    obtain ⟨b, hb⟩ := hK a ha
    exact resLe_cls_zero K (n + 1) a ha ⟨b, by rw [hb, one_smul]⟩
  constructor
  · rintro ⟨-, hs⟩ y hy
    obtain ⟨x, hx⟩ := hs (L.cls y hy)
    rw [hz x, map_zero] at hx
    have hy' : L.d (n + 1) (s • y) = 0 := by rw [map_smul, hy, smul_zero]
    rw [← resLe_cls_smul L (n + 1) s y hy hy'] at hx
    have : s • y ∈ L.B (n + 1) := ((CrystallineSemistableComparison.P.cls_surj L (n + 1)).2.1 _ hy').1 hx.symm
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc⟩
  · intro h
    refine ⟨fun x _ => by rw [hz x, smul_zero], fun y => ⟨0, ?_⟩⟩
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L (n + 1)).1 y
    have hb' : L.d (n + 1) (s • b) = 0 := by rw [map_smul, hb, smul_zero]
    obtain ⟨c, hc⟩ := h b hb
    rw [map_zero, ← resLe_cls_smul L (n + 1) s b hb hb']
    exact (resLe_cls_zero L (n + 1) _ hb' ⟨c, hc⟩).symm

theorem resLe_zero {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R))
    {M : Type u''} [AddCommGroup M] [Module R M] (ε : M →ₗ[R] K.X 0) (hK : K.ResUpTo 1 ε) (s : R) :
    UpTo s (φ.mapH 0) ↔ InjUpTo s (φ.f 0 ∘ₗ ε) ∧ ExactUpTo s (φ.f 0 ∘ₗ ε) (L.d 0) := by
  obtain ⟨hd, hi, he, -⟩ := hK
  have hLd : ∀ x, L.d 0 (φ.f 0 (ε x)) = 0 := fun x => by rw [φ.comm, hd, map_zero]
  constructor
  · rintro ⟨hI, hS⟩
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · have h1 : φ.mapH 0 (K.cls (ε x) (hd x)) = 0 := by
        rw [CrystallineSemistableComparison.P.mapH_cls φ 0 _ _ (hLd x)]
        exact resLe_cls_zero L 0 _ _ (by rw [show φ.f 0 (ε x) = 0 from hx]; exact Submodule.zero_mem _)
      have h2 := hI _ h1
      have hs' : K.d 0 (s • ε x) = 0 := by rw [map_smul, hd, smul_zero]
      rw [← resLe_cls_smul K 0 s _ _ hs'] at h2
      have h3 : s • ε x = 0 := eq_zero_of_mem_boundaries_zero _ _ (((CrystallineSemistableComparison.P.cls_surj K 0).2.1 _ hs').1 h2)
      rw [← map_smul] at h3
      have := hi _ h3
      rwa [one_smul] at this
    · obtain ⟨x, hx⟩ := hS (L.cls y hy)
      obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K 0).1 x
      obtain ⟨m, hm⟩ := he a ha
      rw [one_smul] at hm
      refine ⟨m, ?_⟩
      have hy' : L.d 0 (s • y) = 0 := by rw [map_smul, hy, smul_zero]
      have hfa : L.d 0 (φ.f 0 a) = 0 := by rw [φ.comm, ha, map_zero]
      rw [CrystallineSemistableComparison.P.mapH_cls φ 0 a ha hfa, ← resLe_cls_smul L 0 s y hy hy'] at hx
      have := ((CrystallineSemistableComparison.P.cls_surj L 0).2.2.1 _ _ hfa hy').1 hx
      change φ.f 0 (ε m) = s • y
      rw [hm]
      exact sub_eq_zero.1 (eq_zero_of_mem_boundaries_zero _ _ this)
  · rintro ⟨hI, hE⟩
    refine ⟨fun x hx => ?_, fun y => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K 0).1 x
      have hfa : L.d 0 (φ.f 0 a) = 0 := by rw [φ.comm, ha, map_zero]
      rw [CrystallineSemistableComparison.P.mapH_cls φ 0 a ha hfa] at hx
      have h0 : φ.f 0 a = 0 := eq_zero_of_mem_boundaries_zero _ _ (((CrystallineSemistableComparison.P.cls_surj L 0).2.1 _ hfa).1 hx)
      obtain ⟨m, hm⟩ := he a ha
      rw [one_smul] at hm
      have h1 : s • m = 0 := hI m (by change φ.f 0 (ε m) = 0; rw [hm, h0])
      have hs' : K.d 0 (s • a) = 0 := by rw [map_smul, ha, smul_zero]
      rw [← resLe_cls_smul K 0 s a ha hs']
      exact resLe_cls_zero K 0 _ hs' (by rw [← hm, ← map_smul, h1, map_zero]; exact Submodule.zero_mem _)
    · obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L 0).1 y
      obtain ⟨m, hm⟩ := hE b hb
      refine ⟨K.cls (ε m) (hd m), ?_⟩
      have hb' : L.d 0 (s • b) = 0 := by rw [map_smul, hb, smul_zero]
      rw [CrystallineSemistableComparison.P.mapH_cls φ 0 _ _ (hLd m), ← resLe_cls_smul L 0 s b hb hb']
      exact ((CrystallineSemistableComparison.P.cls_surj L 0).2.2.1 _ _ _ hb').2 (by
        rw [show φ.f 0 (ε m) = s • b from hm, sub_self]; exact Submodule.zero_mem _)

theorem resLe_cx {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R))
    {M : Type u''} [AddCommGroup M] [Module R M] (ε : M →ₗ[R] K.X 0) (hK : K.ResUpTo 1 ε) (s : R) :
    L.ResUpTo s (φ.f 0 ∘ₗ ε) ↔ ∀ n, UpTo s (φ.mapH n) := by
  have hd : ∀ x, L.d 0 ((φ.f 0 ∘ₗ ε) x) = 0 := fun x => by
    change L.d 0 (φ.f 0 (ε x)) = 0
    rw [φ.comm, hK.1, map_zero]
  constructor
  · rintro ⟨-, hi, he, hn⟩ n
    cases n with
    | zero => exact (resLe_zero φ ε hK s).2 ⟨hi, he⟩
    | succ n => exact (resLe_succ φ n (hK.2.2.2 n) s).2 (hn n)
  · intro h
    obtain ⟨hi, he⟩ := (resLe_zero φ ε hK s).1 (h 0)
    exact ⟨hd, hi, he, fun n => (resLe_succ φ n (hK.2.2.2 n) s).1 (h (n + 1))⟩

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.res_le : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C ⥤ ModuleCat.{w} R) (F' : C' ⥤ ModuleCat.{w'} R) (m : Mor F F' (RingHom.id R)) (T₀ : C) (h : Limits.IsInitial T₀) (s : R), ((cx F').ResUpTo s (aug F' fun T => (m.τ T) ∘ₗ (F.map (h.to _)).hom) ↔ ∀ n, UpTo s (m.pull n)) := by
  intro R _ C _ C' _ F F' m T₀ h s
  have e : (aug F' fun T => (m.τ T) ∘ₗ (F.map (h.to _)).hom) = m.hom.f 0 ∘ₗ aug F fun T => (F.map (h.to T)).hom := by
    apply LinearMap.ext; intro x; funext c; rfl
  rw [e]
  exact CrystallineSemistableComparison.B.resLe_cx m.hom _ (CrystallineSemistableComparison.P.initial F T₀ h) s
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FRiCalc
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

lemma rc_pull_comp {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {C'' : Type u''} [Category.{v''} C''] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w} R}
    {F'' : C'' ⥤ ModuleCat.{w} R} (m : Mor F F' (RingHom.id R)) (m' : Mor F' F'' (RingHom.id R)) (n : ℕ) :
    (m.comp m' : Mor F F'' (RingHom.id R)).pull n = (m'.pull n).comp (m.pull n) :=
  LinearMap.ext fun x => (CrystallineSemistableComparison.P.pull_comp m m' n x).1

lemma rc_restrict_comp {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {C'' : Type u''} [Category.{v''} C''] (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) (G' : C'' ⥤ C') (n : ℕ) :
    (Mor.restrict F (G' ⋙ G)).pull n = ((Mor.restrict (G ⋙ F) G').pull n).comp ((Mor.restrict F G).pull n) :=
  rc_pull_comp (Mor.restrict F G) (Mor.restrict (G ⋙ F) G') n

lemma rc_iso_upTo {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F F₁ : C ⥤ ModuleCat.{w} R}
    (e : F ≅ F₁) (n : ℕ) : UpTo (1 : R) ((Mor.ofNatTrans e.hom).pull n) := by
  have h := CrystallineSemistableComparison.P.coef_upTo e.hom (1 : R) (fun T => by
    refine ((CrystallineSemistableComparison.P.upTo_alg (e.hom.app T).hom LinearMap.id 1 1).2.2.2.2).2 ?_
    exact (e.app T).toLinearEquiv.bijective) n
  rwa [one_pow] at h

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.ri_calc : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C''] (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) (G' : C'' ⥤ C') (s s' : R) (n : ℕ), (RI s n F G → RI s' n (G ⋙ F) G' → RI (s * s') n F (G' ⋙ G)) ∧ (RI s n F G → RI s' n F (G' ⋙ G) → RI (s * s') n (G ⋙ F) G') ∧ (RI s n (G ⋙ F) G' → RI s' n F (G' ⋙ G) → RI (s * s') n F G) ∧ (RI s n F G → RI (s * s') n F G) ∧ (∀ G₁ : C' ⥤ C, (G ≅ G₁) → RI s n F G → RI s n F G₁) ∧ (G.IsEquivalence → RI 1 n F G) ∧ (∀ F₁ : C ⥤ ModuleCat.{w} R, (F ≅ F₁) → RI s n F G → RI s n F₁ G) := by
  intro R _ C _ C' _ C'' _ F G G' s s' n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1 h2 j hj
    rw [RI, IsoLe] at *
    rw [rc_restrict_comp]
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ s s').1 (h1 j hj) (h2 j hj)
  · intro h1 h2 j hj
    have := h2 j hj
    rw [rc_restrict_comp] at this
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ s s').2.1 (h1 j hj) this
  · intro h1 h2 j hj
    have := h2 j hj
    rw [rc_restrict_comp] at this
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ s s').2.2.1 (h1 j hj) this
  · intro h1 j hj
    exact (CrystallineSemistableComparison.P.upTo_alg ((Mor.restrict F G).pull j) LinearMap.id s s').2.2.2.1 (h1 j hj)
  · intro G₁ e h1 j hj
    have hp : (Mor.restrict F G₁).pull j =
        ((Mor.ofNatTrans (Functor.whiskerRight e.hom F)).pull j).comp ((Mor.restrict F G).pull j) := by
      rw [← rc_pull_comp]
      refine LinearMap.ext fun x => CrystallineSemistableComparison.P.prism (Mor.restrict F G₁)
        ((Mor.restrict F G).comp (Mor.ofNatTrans (Functor.whiskerRight e.hom F))) e.inv ?_ j x
      intro T x
      change (F.map (e.hom.app T)).hom ((F.map (e.inv.app T)).hom x) = x
      rw [← ModuleCat.comp_apply, ← F.map_comp, e.inv_hom_id_app, F.map_id]
      rfl
    rw [hp, ← mul_one s]
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ s 1).1 (h1 j hj) (rc_iso_upTo (Functor.isoWhiskerRight e F) j)
  · intro hG j hj
    exact ((CrystallineSemistableComparison.P.upTo_alg ((Mor.restrict F G).pull j) LinearMap.id 1 1).2.2.2.2).2
      (CrystallineSemistableComparison.P.adj F G G.asEquivalence.inverse G.asEquivalence.toAdjunction j)
  · intro F₁ e h1 j hj
    have hp : (Mor.restrict F₁ G).pull j =
        ((Mor.ofNatTrans (Functor.whiskerLeft G e.hom)).pull j).comp
          (((Mor.restrict F G).pull j).comp ((Mor.ofNatTrans e.inv).pull j)) := by
      rw [← rc_pull_comp, ← rc_pull_comp]
      refine LinearMap.ext fun x => CrystallineSemistableComparison.P.prism (Mor.restrict F₁ G)
        ((Mor.ofNatTrans e.inv).comp ((Mor.restrict F G).comp (Mor.ofNatTrans (Functor.whiskerLeft G e.hom))))
        (𝟙 G) ?_ j x
      intro T x
      change (e.hom.app (G.obj T)).hom ((e.inv.app (G.obj T)).hom ((F₁.map (𝟙 (G.obj T))).hom x)) = x
      rw [F₁.map_id, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, e.inv_hom_id_app]
      rfl
    rw [hp, ← one_mul s, ← mul_one (1 * s)]
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ (1 * s) 1).1
      ((CrystallineSemistableComparison.P.upTo_alg _ _ 1 s).1 (rc_iso_upTo e.symm j) (h1 j hj))
      (rc_iso_upTo (Functor.isoWhiskerLeft G e) j)
end

