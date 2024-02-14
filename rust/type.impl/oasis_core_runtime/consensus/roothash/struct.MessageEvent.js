(function() {var type_impls = {
"oasis_runtime_sdk":[["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Clone-for-MessageEvent\" class=\"impl\"><a class=\"src rightside\" href=\"src/oasis_core_runtime/consensus/roothash/mod.rs.html#92\">source</a><a href=\"#impl-Clone-for-MessageEvent\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"oasis_core_runtime/consensus/roothash/struct.MessageEvent.html\" title=\"struct oasis_core_runtime::consensus::roothash::MessageEvent\">MessageEvent</a></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/oasis_core_runtime/consensus/roothash/mod.rs.html#92\">source</a><a href=\"#method.clone\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\" class=\"fn\">clone</a>(&amp;self) -&gt; <a class=\"struct\" href=\"oasis_core_runtime/consensus/roothash/struct.MessageEvent.html\" title=\"struct oasis_core_runtime::consensus::roothash::MessageEvent\">MessageEvent</a></h4></section></summary><div class='docblock'>Returns a copy of the value. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone_from\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/clone.rs.html#169\">source</a></span><a href=\"#method.clone_from\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\" class=\"fn\">clone_from</a>(&amp;mut self, source: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;Self</a>)</h4></section></summary><div class='docblock'>Performs copy-assignment from <code>source</code>. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\">Read more</a></div></details></div></details>","Clone","oasis_runtime_sdk::types::message::MessageEvent"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Debug-for-MessageEvent\" class=\"impl\"><a class=\"src rightside\" href=\"src/oasis_core_runtime/consensus/roothash/mod.rs.html#92\">source</a><a href=\"#impl-Debug-for-MessageEvent\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a> for <a class=\"struct\" href=\"oasis_core_runtime/consensus/roothash/struct.MessageEvent.html\" title=\"struct oasis_core_runtime::consensus::roothash::MessageEvent\">MessageEvent</a></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.fmt\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/oasis_core_runtime/consensus/roothash/mod.rs.html#92\">source</a><a href=\"#method.fmt\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html#tymethod.fmt\" class=\"fn\">fmt</a>(&amp;self, f: &amp;mut <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/core/fmt/struct.Formatter.html\" title=\"struct core::fmt::Formatter\">Formatter</a>&lt;'_&gt;) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.unit.html\">()</a>, <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/core/fmt/struct.Error.html\" title=\"struct core::fmt::Error\">Error</a>&gt;</h4></section></summary><div class='docblock'>Formats the value using the given formatter. <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html#tymethod.fmt\">Read more</a></div></details></div></details>","Debug","oasis_runtime_sdk::types::message::MessageEvent"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Decode-for-MessageEvent\" class=\"impl\"><a class=\"src rightside\" href=\"src/oasis_core_runtime/consensus/roothash/mod.rs.html#92\">source</a><a href=\"#impl-Decode-for-MessageEvent\" class=\"anchor\">§</a><h3 class=\"code-header\">impl Decode for <a class=\"struct\" href=\"oasis_core_runtime/consensus/roothash/struct.MessageEvent.html\" title=\"struct oasis_core_runtime::consensus::roothash::MessageEvent\">MessageEvent</a></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.try_default\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/oasis_core_runtime/consensus/roothash/mod.rs.html#92\">source</a><a href=\"#method.try_default\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a class=\"fn\">try_default</a>() -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;<a class=\"struct\" href=\"oasis_core_runtime/consensus/roothash/struct.MessageEvent.html\" title=\"struct oasis_core_runtime::consensus::roothash::MessageEvent\">MessageEvent</a>, DecodeError&gt;</h4></section></summary><div class='docblock'>Try to decode from a missing/null/undefined value.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.try_from_cbor_value\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/oasis_core_runtime/consensus/roothash/mod.rs.html#92\">source</a><a href=\"#method.try_from_cbor_value\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a class=\"fn\">try_from_cbor_value</a>(value: Value) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;<a class=\"struct\" href=\"oasis_core_runtime/consensus/roothash/struct.MessageEvent.html\" title=\"struct oasis_core_runtime::consensus::roothash::MessageEvent\">MessageEvent</a>, DecodeError&gt;</h4></section></summary><div class='docblock'>Try to decode from a given CBOR value.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.try_from_cbor_value_default\" class=\"method trait-impl\"><a href=\"#method.try_from_cbor_value_default\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a class=\"fn\">try_from_cbor_value_default</a>(value: Value) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;Self, DecodeError&gt;<div class=\"where\">where\n    Self: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h4></section></summary><div class='docblock'>Try to decode from a given CBOR value, calling <code>try_default</code> in case the value is null or\nundefined.</div></details></div></details>","Decode","oasis_runtime_sdk::types::message::MessageEvent"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Default-for-MessageEvent\" class=\"impl\"><a class=\"src rightside\" href=\"src/oasis_core_runtime/consensus/roothash/mod.rs.html#92\">source</a><a href=\"#impl-Default-for-MessageEvent\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"oasis_core_runtime/consensus/roothash/struct.MessageEvent.html\" title=\"struct oasis_core_runtime::consensus::roothash::MessageEvent\">MessageEvent</a></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.default\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/oasis_core_runtime/consensus/roothash/mod.rs.html#92\">source</a><a href=\"#method.default\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html#tymethod.default\" class=\"fn\">default</a>() -&gt; <a class=\"struct\" href=\"oasis_core_runtime/consensus/roothash/struct.MessageEvent.html\" title=\"struct oasis_core_runtime::consensus::roothash::MessageEvent\">MessageEvent</a></h4></section></summary><div class='docblock'>Returns the “default value” for a type. <a href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html#tymethod.default\">Read more</a></div></details></div></details>","Default","oasis_runtime_sdk::types::message::MessageEvent"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Encode-for-MessageEvent\" class=\"impl\"><a class=\"src rightside\" href=\"src/oasis_core_runtime/consensus/roothash/mod.rs.html#92\">source</a><a href=\"#impl-Encode-for-MessageEvent\" class=\"anchor\">§</a><h3 class=\"code-header\">impl Encode for <a class=\"struct\" href=\"oasis_core_runtime/consensus/roothash/struct.MessageEvent.html\" title=\"struct oasis_core_runtime::consensus::roothash::MessageEvent\">MessageEvent</a></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.into_cbor_value\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/oasis_core_runtime/consensus/roothash/mod.rs.html#92\">source</a><a href=\"#method.into_cbor_value\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a class=\"fn\">into_cbor_value</a>(self) -&gt; Value</h4></section></summary><div class='docblock'>Encode the type into a CBOR Value.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.is_empty\" class=\"method trait-impl\"><a href=\"#method.is_empty\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a class=\"fn\">is_empty</a>(&amp;self) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>Whether the value is equal to the empty value for the type.</div></details></div></details>","Encode","oasis_runtime_sdk::types::message::MessageEvent"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-EncodeAsMap-for-MessageEvent\" class=\"impl\"><a class=\"src rightside\" href=\"src/oasis_core_runtime/consensus/roothash/mod.rs.html#92\">source</a><a href=\"#impl-EncodeAsMap-for-MessageEvent\" class=\"anchor\">§</a><h3 class=\"code-header\">impl EncodeAsMap for <a class=\"struct\" href=\"oasis_core_runtime/consensus/roothash/struct.MessageEvent.html\" title=\"struct oasis_core_runtime::consensus::roothash::MessageEvent\">MessageEvent</a></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.into_cbor_value_map\" class=\"method trait-impl\"><a href=\"#method.into_cbor_value_map\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a class=\"fn\">into_cbor_value_map</a>(self) -&gt; Value<div class=\"where\">where\n    Self: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h4></section></summary><div class='docblock'>Encode the type into a CBOR Map.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.into_cbor_map\" class=\"method trait-impl\"><a href=\"#method.into_cbor_map\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a class=\"fn\">into_cbor_map</a>(self) -&gt; <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/alloc/vec/struct.Vec.html\" title=\"struct alloc::vec::Vec\">Vec</a>&lt;(Value, Value)&gt;<div class=\"where\">where\n    Self: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h4></section></summary><div class='docblock'>Encode the type into a CBOR Map, returning the map items.</div></details></div></details>","EncodeAsMap","oasis_runtime_sdk::types::message::MessageEvent"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-MessageEvent\" class=\"impl\"><a class=\"src rightside\" href=\"src/oasis_core_runtime/consensus/roothash/mod.rs.html#107\">source</a><a href=\"#impl-MessageEvent\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"struct\" href=\"oasis_core_runtime/consensus/roothash/struct.MessageEvent.html\" title=\"struct oasis_core_runtime::consensus::roothash::MessageEvent\">MessageEvent</a></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.is_success\" class=\"method\"><a class=\"src rightside\" href=\"src/oasis_core_runtime/consensus/roothash/mod.rs.html#109\">source</a><h4 class=\"code-header\">pub fn <a href=\"oasis_core_runtime/consensus/roothash/struct.MessageEvent.html#tymethod.is_success\" class=\"fn\">is_success</a>(&amp;self) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section></summary><div class=\"docblock\"><p>Returns true if the event indicates that the message was successfully processed.</p>\n</div></details></div></details>",0,"oasis_runtime_sdk::types::message::MessageEvent"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-PartialEq-for-MessageEvent\" class=\"impl\"><a class=\"src rightside\" href=\"src/oasis_core_runtime/consensus/roothash/mod.rs.html#92\">source</a><a href=\"#impl-PartialEq-for-MessageEvent\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html\" title=\"trait core::cmp::PartialEq\">PartialEq</a> for <a class=\"struct\" href=\"oasis_core_runtime/consensus/roothash/struct.MessageEvent.html\" title=\"struct oasis_core_runtime::consensus::roothash::MessageEvent\">MessageEvent</a></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.eq\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/oasis_core_runtime/consensus/roothash/mod.rs.html#92\">source</a><a href=\"#method.eq\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html#tymethod.eq\" class=\"fn\">eq</a>(&amp;self, other: &amp;<a class=\"struct\" href=\"oasis_core_runtime/consensus/roothash/struct.MessageEvent.html\" title=\"struct oasis_core_runtime::consensus::roothash::MessageEvent\">MessageEvent</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>This method tests for <code>self</code> and <code>other</code> values to be equal, and is used\nby <code>==</code>.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.ne\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/cmp.rs.html#263\">source</a></span><a href=\"#method.ne\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html#method.ne\" class=\"fn\">ne</a>(&amp;self, other: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;Rhs</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>This method tests for <code>!=</code>. The default implementation is almost always\nsufficient, and should not be overridden without very good reason.</div></details></div></details>","PartialEq","oasis_runtime_sdk::types::message::MessageEvent"],["<section id=\"impl-Eq-for-MessageEvent\" class=\"impl\"><a class=\"src rightside\" href=\"src/oasis_core_runtime/consensus/roothash/mod.rs.html#92\">source</a><a href=\"#impl-Eq-for-MessageEvent\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Eq.html\" title=\"trait core::cmp::Eq\">Eq</a> for <a class=\"struct\" href=\"oasis_core_runtime/consensus/roothash/struct.MessageEvent.html\" title=\"struct oasis_core_runtime::consensus::roothash::MessageEvent\">MessageEvent</a></h3></section>","Eq","oasis_runtime_sdk::types::message::MessageEvent"],["<section id=\"impl-StructuralPartialEq-for-MessageEvent\" class=\"impl\"><a class=\"src rightside\" href=\"src/oasis_core_runtime/consensus/roothash/mod.rs.html#92\">source</a><a href=\"#impl-StructuralPartialEq-for-MessageEvent\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.StructuralPartialEq.html\" title=\"trait core::marker::StructuralPartialEq\">StructuralPartialEq</a> for <a class=\"struct\" href=\"oasis_core_runtime/consensus/roothash/struct.MessageEvent.html\" title=\"struct oasis_core_runtime::consensus::roothash::MessageEvent\">MessageEvent</a></h3></section>","StructuralPartialEq","oasis_runtime_sdk::types::message::MessageEvent"]]
};if (window.register_type_impls) {window.register_type_impls(type_impls);} else {window.pending_type_impls = type_impls;}})()