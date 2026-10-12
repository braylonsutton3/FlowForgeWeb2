FROM mcr.microsoft.com/playwright/python:v1.55.0-noble
WORKDIR /app
ENV PYTHONUNBUFFERED=1
ENV PLAYWRIGHT_BROWSERS_PATH=/ms-playwright
COPY requirements.txt ./
RUN pip install --no-cache-dir -r requirements.txt
COPY main.py ./
EXPOSE 10000
CMD ["sh", "-c", "exec gunicorn main:app --bind 0.0.0.0:${PORT:-10000} --worker-class gthread --workers 1 --threads 4 --timeout 120"]
