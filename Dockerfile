FROM swipl:stable
COPY . /app
RUN swipl /app/uvl.pl
