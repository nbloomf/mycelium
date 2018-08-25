files = \
  doc/Mycelium.html \
  doc/Var.html \
  doc/Sub.html \
  doc/Expr.html \
  doc/Type.html \
  doc/Infer.html \
  doc/Jud.html \
  doc/Proof.html \
  doc/Module.html \
  doc/Fancy.html \
  doc/Parser.html

docs: $(files) doc/Tests.html doc/Main.html

doc/%.html: src/%.lhs
	pandoc --mathjax -s -c style.css -o $@ $<

doc/Tests.html: test/Tests.lhs
	pandoc --mathjax -s -c style.css -o $@ $<

doc/Main.html: app/Main.lhs
	pandoc --mathjax -s -c style.css -o $@ $<
