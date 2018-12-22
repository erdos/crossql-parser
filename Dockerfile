FROM haskell:8
COPY . /app
WORKDIR /app
RUN ghc -O3 Main.hs

FROM phusion/baseimage
WORKDIR /app
COPY --from=0 /app /app
CMD /app/Main
