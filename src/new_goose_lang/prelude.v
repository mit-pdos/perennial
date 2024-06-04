From Perennial.goose_lang Require Export lang notation typing.
From Perennial.new_goose_lang Require Export exception loop.impl.
From Perennial.goose_lang.lib Require Export
     typed_mem.impl struct.impl
     encoding.impl map.impl slice.impl
     time.impl rand.impl string.impl channel.impl
     noop.impl
.

Open Scope heap_types.
Open Scope struct_scope.
