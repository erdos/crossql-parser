FROM haskell:8

RUN cabal update && cabal install wai warp

COPY . /app
WORKDIR /app

RUN ghc -O3 Service.hs

FROM phusion/baseimage
# RUN apt-get install libc6
WORKDIR /app
COPY --from=0 /app /app
CMD /app/Service
