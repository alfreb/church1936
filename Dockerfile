FROM ubuntu:latest
WORKDIR /opt/example

RUN apt update
RUN apt install -y ghc cabal-install locales

# Add unicode support 
RUN sed -i '/en_US.UTF-8/s/^# //g' /etc/locale.gen && \
    locale-gen

ENV LANG en_US.UTF-8  
ENV LANGUAGE en_US:en  
ENV LC_ALL en_US.UTF-8    

RUN cabal update 

# Add just the .cabal file to capture dependencies
COPY ./church1936.cabal /opt/example/church1936.cabal
RUN cabal build --only-dependencies --enable-tests --enable-benchmarks -j8

# Add and build application code, install test dependency
COPY . /opt/example
RUN cabal install hspec-discover
RUN cabal build

CMD ["cabal", "run", "church1936"],