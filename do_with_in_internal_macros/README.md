# Do With In (internal macros package)

This is an inner package that contains the proc\_macros that most end users will use. Do not use it directly. The package do-with-in reexports everything that forms the public interface. Splitting the packages this way was necessary so that do-with-in could reexport both proc\_macros from this package and the items they were built from in the package do-with-in-base.
